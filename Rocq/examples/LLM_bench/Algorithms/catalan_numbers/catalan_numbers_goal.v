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
Require Import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function id -----*)

Definition id_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (((x_pre * (n_pre + 1 ) ) + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x_pre * (n_pre + 1 ) ) + y_pre )) ”
.

Definition id_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((x_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * (n_pre + 1 ) )) ”
.

Definition id_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition id_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition id_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  TT && emp 
|--
  “ (((x_pre * (n_pre + 1 ) ) + y_pre ) = ((x_pre * (n_pre + 1 ) ) + y_pre )) ” 
  &&  “ (0 <= ((x_pre * (n_pre + 1 ) ) + y_pre )) ” 
  &&  “ (((x_pre * (n_pre + 1 ) ) + y_pre ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  TT && emp 
|--
  “ (((x_pre * (n_pre + 1 ) ) + y_pre ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition id_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (0 <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1 ))) ,
  (((x_pre * (n_pre + 1 ) ) + y_pre ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))
.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (f_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  (IntArray.undef_full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_2 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (StackRowsDone n_pre table i )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f_pre 0 (i * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre (i * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_3 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j <= (n_pre + 1 ))) (PreH8 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_4 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_5 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (j: Z) (i: Z) (PreH1 : (i <> 0)) (PreH2 : (j <= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_6 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = 0)) (PreH9 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH12 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solve_safety_wit_7 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = 0)) (PreH9 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH12 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solve_safety_wit_8 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = 0)) (PreH9 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH12 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_9 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = 0)) (PreH9 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH12 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_10 := 
(
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval_3 = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (((Znth (retval - 0 ) table 0) + (Znth (retval_2 - 0 ) table 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (retval - 0 ) table 0) + (Znth (retval_2 - 0 ) table 0) )) ”
) \/
(
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval_3 = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (((Znth (retval - 0 ) table 0) + (Znth (retval_2 - 0 ) table 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (retval - 0 ) table 0) + (Znth (retval_2 - 0 ) table 0) )) ”
).

Definition solve_safety_wit_10_split_goal_1 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval_3 = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (((Znth (retval - 0 ) table 0) + (Znth (retval_2 - 0 ) table 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_10_split_goal_2 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval_3 = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((INT_MIN) <= ((Znth (retval - 0 ) table 0) + (Znth (retval_2 - 0 ) table 0) )) ”
.

Definition solve_safety_wit_11 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH13 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH15 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solve_safety_wit_12 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH13 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH15 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solve_safety_wit_13 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH13 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH15 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_14 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH13 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH15 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_15 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH16 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH18 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH19 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solve_safety_wit_16 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH16 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH18 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH19 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_17 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) )) (PreH8 : (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) )) (PreH9 : (StackRowProgress n_pre table i (j + 1 ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) table )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solve_safety_wit_18 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (StackRowsDone n_pre table (i + 1 ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f_pre 0 ((i + 1 ) * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre ((i + 1 ) * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_19 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH4 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH5 : (StackRowsDone n_pre table (n_pre + 1 ) )) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_entail_wit_1 := 
(
forall (f_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  (IntArray.undef_full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (StackRowsDone n_pre table 0 ) ”
  &&  (IntArray.seg f_pre 0 (0 * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre (0 * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (f_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  (IntArray.undef_full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (StackRowsDone n_pre table 0 ) ”
  &&  (IntArray.seg f_pre 0 (0 * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre (0 * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
).

Definition solve_entail_wit_2 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (StackRowsDone n_pre table_2 i )) ,
  (IntArray.seg f_pre 0 (i * (n_pre + 1 ) ) table_2 )
  **  (IntArray.undef_seg f_pre (i * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (StackRowProgress n_pre table i 0 ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + 0 ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + 0 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (StackRowsDone n_pre table_2 i )) ,
  (IntArray.seg f_pre 0 (i * (n_pre + 1 ) ) table_2 )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (StackRowProgress n_pre table i 0 ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + 0 ) table )
).

Definition solve_entail_wit_3 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table_2 )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  TT && emp 
|--
  “ ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) < ((i * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + 0 ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition solve_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) < ((i * (n_pre + 1 ) ) + 0 ))
.

Definition solve_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  (((i * (n_pre + 1 ) ) + 0 ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition solve_entail_wit_4 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table_2 )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  TT && emp 
|--
  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition solve_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))
.

Definition solve_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= (n_pre + 1 ))) (PreH10 : (StackRowProgress n_pre table_2 i j )) ,
  (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition solve_entail_wit_5_1 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) (app (table_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) ) ” 
  &&  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) ) ” 
  &&  “ (StackRowProgress n_pre table i (j + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) table )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table_2 i j )) ,
  TT && emp 
|--
  “ (StackRowProgress n_pre (app (table_2) ((cons (1) ((@nil Z))))) 0 (j + 1 ) ) ” 
  &&  “ (StackCellCorrect n_pre 0 j (Znth ((0 * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (1) ((@nil Z))))) 0) ) ” 
  &&  “ (StackCellBound 0 j (Znth ((0 * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (1) ((@nil Z))))) 0) ) ”
  &&  emp
).

Definition solve_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table_2 i j )) ,
  (StackRowProgress n_pre (app (table_2) ((cons (1) ((@nil Z))))) 0 (j + 1 ) )
.

Definition solve_entail_wit_5_1_split_goal_2 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table_2 i j )) ,
  (StackCellCorrect n_pre 0 j (Znth ((0 * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (1) ((@nil Z))))) 0) )
.

Definition solve_entail_wit_5_1_split_goal_3 := 
forall (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table_2 i j )) ,
  (StackCellBound 0 j (Znth ((0 * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (1) ((@nil Z))))) 0) )
.

Definition solve_entail_wit_5_2 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) (app (table_2) ((cons ((Znth (retval_2 - 0 ) table_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) ) ” 
  &&  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) ) ” 
  &&  “ (StackRowProgress n_pre table i (j + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) table )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table_2 i j )) ,
  TT && emp 
|--
  “ (StackRowProgress n_pre (app (table_2) ((cons ((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) - 0 ) table_2 0)) ((@nil Z))))) i (0 + 1 ) ) ” 
  &&  “ (StackCellCorrect n_pre i 0 (Znth ((i * (n_pre + 1 ) ) + 0 ) (app (table_2) ((cons ((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) - 0 ) table_2 0)) ((@nil Z))))) 0) ) ” 
  &&  “ (StackCellBound i 0 (Znth ((i * (n_pre + 1 ) ) + 0 ) (app (table_2) ((cons ((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) - 0 ) table_2 0)) ((@nil Z))))) 0) ) ”
  &&  emp
).

Definition solve_entail_wit_5_2_split_goal_1 := 
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table_2 i j )) ,
  (StackRowProgress n_pre (app (table_2) ((cons ((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) - 0 ) table_2 0)) ((@nil Z))))) i (0 + 1 ) )
.

Definition solve_entail_wit_5_2_split_goal_2 := 
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table_2 i j )) ,
  (StackCellCorrect n_pre i 0 (Znth ((i * (n_pre + 1 ) ) + 0 ) (app (table_2) ((cons ((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) - 0 ) table_2 0)) ((@nil Z))))) 0) )
.

Definition solve_entail_wit_5_2_split_goal_3 := 
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table_2 i j )) ,
  (StackCellBound i 0 (Znth ((i * (n_pre + 1 ) ) + 0 ) (app (table_2) ((cons ((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (0 + 1 ) ) - 0 ) table_2 0)) ((@nil Z))))) 0) )
.

Definition solve_entail_wit_5_3 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) (app (table_2) ((cons (((Znth (retval_2 - 0 ) table_2 0) + (Znth (retval_3 - 0 ) table_2 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) ) ” 
  &&  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) table 0) ) ” 
  &&  “ (StackRowProgress n_pre table i (j + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) table )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table_2 i j )) ,
  TT && emp 
|--
  “ (StackRowProgress n_pre (app (table_2) ((cons (((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) - 0 ) table_2 0) + (Znth (((i * (n_pre + 1 ) ) + (j - 1 ) ) - 0 ) table_2 0) )) ((@nil Z))))) i (j + 1 ) ) ” 
  &&  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) - 0 ) table_2 0) + (Znth (((i * (n_pre + 1 ) ) + (j - 1 ) ) - 0 ) table_2 0) )) ((@nil Z))))) 0) ) ” 
  &&  “ (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) - 0 ) table_2 0) + (Znth (((i * (n_pre + 1 ) ) + (j - 1 ) ) - 0 ) table_2 0) )) ((@nil Z))))) 0) ) ”
  &&  emp
).

Definition solve_entail_wit_5_3_split_goal_1 := 
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table_2 i j )) ,
  (StackRowProgress n_pre (app (table_2) ((cons (((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) - 0 ) table_2 0) + (Znth (((i * (n_pre + 1 ) ) + (j - 1 ) ) - 0 ) table_2 0) )) ((@nil Z))))) i (j + 1 ) )
.

Definition solve_entail_wit_5_3_split_goal_2 := 
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table_2 i j )) ,
  (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) - 0 ) table_2 0) + (Znth (((i * (n_pre + 1 ) ) + (j - 1 ) ) - 0 ) table_2 0) )) ((@nil Z))))) 0) )
.

Definition solve_entail_wit_5_3_split_goal_3 := 
forall (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table_2 i j )) ,
  (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) (app (table_2) ((cons (((Znth ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) - 0 ) table_2 0) + (Znth (((i * (n_pre + 1 ) ) + (j - 1 ) ) - 0 ) table_2 0) )) ((@nil Z))))) 0) )
.

Definition solve_entail_wit_6 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) table_2 0) )) (PreH8 : (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) table_2 0) )) (PreH9 : (StackRowProgress n_pre table_2 i (j + 1 ) )) ,
  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) table_2 )
  **  (IntArray.undef_seg f_pre (((i * (n_pre + 1 ) ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (StackRowProgress n_pre table i (j + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + (j + 1 ) ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + (j + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (StackCellBound i j (Znth ((i * (n_pre + 1 ) ) + j ) table_2 0) )) (PreH8 : (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1 ) ) + j ) table_2 0) )) (PreH9 : (StackRowProgress n_pre table_2 i (j + 1 ) )) ,
  (IntArray.seg f_pre 0 (((i * (n_pre + 1 ) ) + j ) + 1 ) table_2 )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (StackRowProgress n_pre table i (j + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + (j + 1 ) ) table )
).

Definition solve_entail_wit_7 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j <= (n_pre + 1 ))) (PreH8 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table_2 )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (StackRowsDone n_pre table (i + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 ((i + 1 ) * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre ((i + 1 ) * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
) \/
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j <= (n_pre + 1 ))) (PreH8 : (StackRowProgress n_pre table_2 i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table_2 )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (StackRowsDone n_pre table (i + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 ((i + 1 ) * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre ((i + 1 ) * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
).

Definition solve_entail_wit_8 := 
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (StackRowsDone n_pre table_2 (i + 1 ) )) ,
  (IntArray.seg f_pre 0 ((i + 1 ) * (n_pre + 1 ) ) table_2 )
  **  (IntArray.undef_seg f_pre ((i + 1 ) * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (StackRowsDone n_pre table (i + 1 ) ) ”
  &&  (IntArray.seg f_pre 0 ((i + 1 ) * (n_pre + 1 ) ) table )
  **  (IntArray.undef_seg f_pre ((i + 1 ) * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_entail_wit_9 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (StackRowsDone n_pre table_2 i )) ,
  (IntArray.seg f_pre 0 (i * (n_pre + 1 ) ) table_2 )
  **  (IntArray.undef_seg f_pre (i * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (StackRowsDone n_pre table (n_pre + 1 ) ) ” 
  &&  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) ) ”
  &&  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
) \/
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (StackRowsDone n_pre table_2 i )) ,
  (IntArray.seg f_pre 0 (i * (n_pre + 1 ) ) table_2 )
  **  (IntArray.undef_seg f_pre (i * (n_pre + 1 ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (table: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (StackRowsDone n_pre table (n_pre + 1 ) ) ” 
  &&  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) ) ”
  &&  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
).

Definition solve_return_wit_1 := 
(
forall (f_pre: Z) (n_pre: Z) (table_2: (@list Z)) (retval: Z) (PreH1 : (retval = ((n_pre * (n_pre + 1 ) ) + 0 ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (StackRowsDone n_pre table_2 (n_pre + 1 ) )) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table_2 0) )) ,
  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_2 )
|--
  EX (table: (@list Z)) ,
  “ (StackSequenceCount n_pre (Znth retval table_2 0) ) ” 
  &&  “ (StackRowsDone n_pre table (n_pre + 1 ) ) ”
  &&  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
) \/
(
forall (n_pre: Z) (table_2: (@list Z)) (retval: Z) (PreH1 : (retval = ((n_pre * (n_pre + 1 ) ) + 0 ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (StackRowsDone n_pre table_2 (n_pre + 1 ) )) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table_2 0) )) ,
  TT && emp 
|--
  “ (StackSequenceCount n_pre (Znth ((n_pre * (n_pre + 1 ) ) + 0 ) table_2 0) ) ”
  &&  emp
).

Definition solve_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (table_2: (@list Z)) (retval: Z) (PreH1 : (retval = ((n_pre * (n_pre + 1 ) ) + 0 ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (StackRowsDone n_pre table_2 (n_pre + 1 ) )) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table_2 0) )) ,
  (StackSequenceCount n_pre (Znth ((n_pre * (n_pre + 1 ) ) + 0 ) table_2 0) )
.

Definition solve_partial_solve_wit_1_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (j: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (j <= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_1_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (j: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (j <= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (i = 0) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_1 := solve_partial_solve_wit_1_pure -> solve_partial_solve_wit_1_aux.

Definition solve_partial_solve_wit_2 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (i = 0)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= (n_pre + 1 ))) (PreH12 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (i = 0) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i f_pre retval ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
.

Definition solve_partial_solve_wit_3_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (j = 0)) (PreH6 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH7 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH9 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_3_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (j = 0)) (PreH6 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH7 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH9 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_3 := solve_partial_solve_wit_3_pure -> solve_partial_solve_wit_3_aux.

Definition solve_partial_solve_wit_4_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = 0)) (PreH9 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH12 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_4_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = 0)) (PreH9 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH10 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH12 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_4 := solve_partial_solve_wit_4_pure -> solve_partial_solve_wit_4_aux.

Definition solve_partial_solve_wit_5 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (((f_pre + (retval_2 * sizeof(INT)))) # Int  |-> (Znth (retval_2 - 0 ) table 0))
  **  (IntArray.missing_i f_pre retval_2 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_6 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = 0)) (PreH12 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH15 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i f_pre retval ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
.

Definition solve_partial_solve_wit_7_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH10 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH12 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_7_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH10 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH12 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH13 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_7 := solve_partial_solve_wit_7_pure -> solve_partial_solve_wit_7_aux.

Definition solve_partial_solve_wit_8_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH13 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH15 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_8_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH11 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH13 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH15 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH16 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_8 := solve_partial_solve_wit_8_pure -> solve_partial_solve_wit_8_aux.

Definition solve_partial_solve_wit_9 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH16 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH18 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH19 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (((f_pre + (retval_2 * sizeof(INT)))) # Int  |-> (Znth (retval_2 - 0 ) table 0))
  **  (IntArray.missing_i f_pre retval_2 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_10_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH16 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH18 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH19 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_10_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH14 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH16 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH18 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH19 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= (n_pre + 1 )) ” 
  &&  “ (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_10 := solve_partial_solve_wit_10_pure -> solve_partial_solve_wit_10_aux.

Definition solve_partial_solve_wit_11 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (((f_pre + (retval_3 * sizeof(INT)))) # Int  |-> (Znth (retval_3 - 0 ) table 0))
  **  (IntArray.missing_i f_pre retval_3 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
.

Definition solve_partial_solve_wit_12 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (i: Z) (j: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (retval = ((i * (n_pre + 1 ) ) + j ))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= ((i * (n_pre + 1 ) ) + j ))) (PreH17 : (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ))) (PreH19 : ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH20 : (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) ))) (PreH21 : (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j ))) (PreH22 : (StackRowProgress n_pre table i j )) ,
  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
  **  (IntArray.undef_seg f_pre ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (retval_3 = ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval_2 = (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) )) ” 
  &&  “ ((((i - 1 ) * (n_pre + 1 ) ) + (j + 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (0 <= ((i * (n_pre + 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((i * (n_pre + 1 ) ) + (j - 1 ) ) < ((i * (n_pre + 1 ) ) + j )) ” 
  &&  “ (StackRowProgress n_pre table i j ) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i f_pre retval ((i * (n_pre + 1 ) ) + j ) ((n_pre + 1 ) * (n_pre + 1 ) ) )
  **  (IntArray.seg f_pre 0 ((i * (n_pre + 1 ) ) + j ) table )
.

Definition solve_partial_solve_wit_13_pure := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH4 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH5 : (StackRowsDone n_pre table (n_pre + 1 ) )) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ”
.

Definition solve_partial_solve_wit_13_aux := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH4 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH5 : (StackRowsDone n_pre table (n_pre + 1 ) )) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) )) ,
  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (StackRowsDone n_pre table (n_pre + 1 ) ) ” 
  &&  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) ) ”
  &&  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
.

Definition solve_partial_solve_wit_13 := solve_partial_solve_wit_13_pure -> solve_partial_solve_wit_13_aux.

Definition solve_partial_solve_wit_14 := 
forall (f_pre: Z) (n_pre: Z) (table: (@list Z)) (retval: Z) (PreH1 : (retval = ((n_pre * (n_pre + 1 ) ) + 0 ))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (StackRowsDone n_pre table (n_pre + 1 ) )) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) )) ,
  (IntArray.full f_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table )
|--
  “ (retval = ((n_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 7) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (StackRowsDone n_pre table (n_pre + 1 ) ) ” 
  &&  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1 ) ) table 0) ) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int  |-> (Znth retval table 0))
  **  (IntArray.missing_i f_pre retval 0 ((n_pre + 1 ) * (n_pre + 1 ) ) table )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_id_safety_wit_1 : id_safety_wit_1.
Axiom proof_of_id_safety_wit_2 : id_safety_wit_2.
Axiom proof_of_id_safety_wit_3 : id_safety_wit_3.
Axiom proof_of_id_safety_wit_4 : id_safety_wit_4.
Axiom proof_of_id_return_wit_1 : id_return_wit_1.
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
Axiom proof_of_solve_safety_wit_15 : solve_safety_wit_15.
Axiom proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Axiom proof_of_solve_safety_wit_17 : solve_safety_wit_17.
Axiom proof_of_solve_safety_wit_18 : solve_safety_wit_18.
Axiom proof_of_solve_safety_wit_19 : solve_safety_wit_19.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Axiom proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1.
Axiom proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2.
Axiom proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Axiom proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3_pure : solve_partial_solve_wit_3_pure.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4_pure : solve_partial_solve_wit_4_pure.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.
Axiom proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6.
Axiom proof_of_solve_partial_solve_wit_7_pure : solve_partial_solve_wit_7_pure.
Axiom proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7.
Axiom proof_of_solve_partial_solve_wit_8_pure : solve_partial_solve_wit_8_pure.
Axiom proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8.
Axiom proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9.
Axiom proof_of_solve_partial_solve_wit_10_pure : solve_partial_solve_wit_10_pure.
Axiom proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10.
Axiom proof_of_solve_partial_solve_wit_11 : solve_partial_solve_wit_11.
Axiom proof_of_solve_partial_solve_wit_12 : solve_partial_solve_wit_12.
Axiom proof_of_solve_partial_solve_wit_13_pure : solve_partial_solve_wit_13_pure.
Axiom proof_of_solve_partial_solve_wit_13 : solve_partial_solve_wit_13.
Axiom proof_of_solve_partial_solve_wit_14 : solve_partial_solve_wit_14.

End VC_Correct.
