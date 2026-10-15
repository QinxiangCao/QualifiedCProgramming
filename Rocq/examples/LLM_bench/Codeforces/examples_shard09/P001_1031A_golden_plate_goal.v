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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P001_1031A_golden_plate_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (PreH1 : (3 <= w_pre)) (PreH2 : (w_pre <= 100)) (PreH3 : (3 <= h_pre)) (PreH4 : (h_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (PreH1 : (3 <= w_pre)) (PreH2 : (w_pre <= 100)) (PreH3 : (3 <= h_pre)) (PreH4 : (h_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |->_)
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((h_pre - (4 * i ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (h_pre - (4 * i ) )) ”
.

Definition solver_safety_wit_4 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |->_)
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((4 * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (4 * i )) ”
.

Definition solver_safety_wit_5 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |->_)
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (4 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 4) ”
.

Definition solver_safety_wit_6 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "W" ) )) # Int64  |->_)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((w_pre - (4 * i ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (w_pre - (4 * i ) )) ”
.

Definition solver_safety_wit_7 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "W" ) )) # Int64  |->_)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((4 * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (4 * i )) ”
.

Definition solver_safety_wit_8 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "W" ) )) # Int64  |->_)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (4 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 4) ”
.

Definition solver_safety_wit_9 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |-> (h_pre - (4 * i ) ))
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) )) ”
.

Definition solver_safety_wit_10 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |-> (h_pre - (4 * i ) ))
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 )) ”
.

Definition solver_safety_wit_11 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |-> (h_pre - (4 * i ) ))
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) )) ”
.

Definition solver_safety_wit_12 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |-> (h_pre - (4 * i ) ))
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) )) ”
.

Definition solver_safety_wit_13 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |-> (h_pre - (4 * i ) ))
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_14 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "H" ) )) # Int64  |-> (h_pre - (4 * i ) ))
  **  ((( &( "W" ) )) # Int64  |-> (w_pre - (4 * i ) ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_15 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (PreH1 : (3 <= w_pre)) (PreH2 : (w_pre <= 100)) (PreH3 : (3 <= h_pre)) (PreH4 : (h_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) ,
  TT && emp 
|--
  “ (3 <= w_pre) ” 
  &&  “ (w_pre <= 100) ” 
  &&  “ (3 <= h_pre) ” 
  &&  “ (h_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 25) ” 
  &&  “ ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 = (((2 * 0 ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * 0 ) * (0 - 1 ) ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10000) ”
  &&  emp
) \/
(
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (PreH1 : (3 <= w_pre)) (PreH2 : (w_pre <= 100)) (PreH3 : (3 <= h_pre)) (PreH4 : (h_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) ,
  TT && emp 
|--
  “ (k_pre <= 25) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (PreH1 : (3 <= w_pre)) (PreH2 : (w_pre <= 100)) (PreH3 : (3 <= h_pre)) (PreH4 : (h_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) ,
  (k_pre <= 25)
.

Definition solver_entail_wit_2 := 
(
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  TT && emp 
|--
  “ (3 <= w_pre) ” 
  &&  “ (w_pre <= 100) ” 
  &&  “ (3 <= h_pre) ” 
  &&  “ (h_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 25) ” 
  &&  “ ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ ((total + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) = (((2 * (i + 1 ) ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * (i + 1 ) ) * ((i + 1 ) - 1 ) ) )) ” 
  &&  “ (0 <= (total + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) )) ” 
  &&  “ ((total + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) <= 10000) ”
  &&  emp
) \/
(
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  TT && emp 
|--
  “ (((((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) <= 10000) ” 
  &&  “ (0 <= ((((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) )) ” 
  &&  “ (((((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) = (((2 * (i + 1 ) ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * (i + 1 ) ) * ((i + 1 ) - 1 ) ) )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  (((((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) <= 10000)
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  (0 <= ((((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ))
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  (((((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) + ((2 * ((w_pre - (4 * i ) ) + (h_pre - (4 * i ) ) ) ) - 4 ) ) = (((2 * (i + 1 ) ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * (i + 1 ) ) * ((i + 1 ) - 1 ) ) ))
.

Definition solver_return_wit_1 := 
(
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  TT && emp 
|--
  “ (Spec w_pre h_pre k_pre total ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  TT && emp 
|--
  “ (Spec w_pre h_pre k_pre (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (h_pre: Z) (w_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (3 <= w_pre)) (PreH3 : (w_pre <= 100)) (PreH4 : (3 <= h_pre)) (PreH5 : (h_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 25)) (PreH8 : ((Z.mul (4) (k_pre)) <= ((Z.min (w_pre) (h_pre)) + 1 ))) (PreH9 : (0 <= i)) (PreH10 : (i <= k_pre)) (PreH11 : (total = (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ))) (PreH12 : (0 <= total)) (PreH13 : (total <= 10000)) ,
  (Spec w_pre h_pre k_pre (((2 * i ) * ((w_pre + h_pre ) - 2 ) ) - ((8 * i ) * (i - 1 ) ) ) )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.

End VC_Correct.
