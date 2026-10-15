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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P091_1063D_candies_for_children_lib.
Local Open Scope sac.

(*----- Function maxll -----*)

Definition maxll_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MaxResult a_pre b_pre a_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MaxResult a_pre b_pre a_pre ) ”
  &&  emp
).

Definition maxll_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  (MaxResult a_pre b_pre a_pre )
.

Definition maxll_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MaxResult a_pre b_pre b_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MaxResult a_pre b_pre b_pre ) ”
  &&  emp
).

Definition maxll_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  (MaxResult a_pre b_pre b_pre )
.

(*----- Function minll -----*)

Definition minll_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MinResult a_pre b_pre a_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MinResult a_pre b_pre a_pre ) ”
  &&  emp
).

Definition minll_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  (MinResult a_pre b_pre a_pre )
.

Definition minll_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MinResult a_pre b_pre b_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (MinResult a_pre b_pre b_pre ) ”
  &&  emp
).

Definition minll_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : ((-1000000000000) <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  (MinResult a_pre b_pre b_pre )
.

(*----- Function ceildiv -----*)

Definition ceildiv_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((-1000000000000) <= a_pre)) (PreH2 : (a_pre <= 1000000000000)) (PreH3 : (1 <= b_pre)) (PreH4 : (b_pre <= 1000000000000)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ceildiv_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ ((a_pre <> (INT64_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition ceildiv_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ ((((a_pre + b_pre ) - 1 ) <> (INT64_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition ceildiv_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ (((a_pre + b_pre ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((a_pre + b_pre ) - 1 )) ”
.

Definition ceildiv_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ ((a_pre + b_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a_pre + b_pre )) ”
.

Definition ceildiv_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ceildiv_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ ((((((a_pre + b_pre ) - 1 ) ÷ b_pre ) - 1 ) * b_pre ) < a_pre) ” 
  &&  “ (a_pre <= ((((a_pre + b_pre ) - 1 ) ÷ b_pre ) * b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (a_pre <= ((((a_pre + b_pre ) - 1 ) ÷ b_pre ) * b_pre )) ” 
  &&  “ ((((((a_pre + b_pre ) - 1 ) ÷ b_pre ) - 1 ) * b_pre ) < a_pre) ”
  &&  emp
).

Definition ceildiv_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  (a_pre <= ((((a_pre + b_pre ) - 1 ) ÷ b_pre ) * b_pre ))
.

Definition ceildiv_return_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((((((a_pre + b_pre ) - 1 ) ÷ b_pre ) - 1 ) * b_pre ) < a_pre)
.

Definition ceildiv_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ ((((a_pre ÷ b_pre ) - 1 ) * b_pre ) < a_pre) ” 
  &&  “ (a_pre <= ((a_pre ÷ b_pre ) * b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  TT && emp 
|--
  “ (a_pre <= ((a_pre ÷ b_pre ) * b_pre )) ” 
  &&  “ ((((a_pre ÷ b_pre ) - 1 ) * b_pre ) < a_pre) ”
  &&  emp
).

Definition ceildiv_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  (a_pre <= ((a_pre ÷ b_pre ) * b_pre ))
.

Definition ceildiv_return_wit_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : ((-1000000000000) <= a_pre)) (PreH3 : (a_pre <= 1000000000000)) (PreH4 : (1 <= b_pre)) (PreH5 : (b_pre <= 1000000000000)) ,
  ((((a_pre ÷ b_pre ) - 1 ) * b_pre ) < a_pre)
.

(*----- Function check -----*)

Definition check_safety_wit_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 100000000000)) (PreH7 : (n_pre <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= (2 * n_pre ))) (PreH10 : (0 <= q_pre)) (PreH11 : (q_pre <= (k_pre - 1 ))) (PreH12 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH13 : ((-1) <= old_best)) (PreH14 : (old_best <= n_pre)) (PreH15 : (0 <= add_pre)) (PreH16 : (add_pre <= 1)) (PreH17 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((( &( "c" ) )) # Int64  |->_)
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((k_pre - x_pre ) + add_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((k_pre - x_pre ) + add_pre )) ”
.

Definition check_safety_wit_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 100000000000)) (PreH7 : (n_pre <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= (2 * n_pre ))) (PreH10 : (0 <= q_pre)) (PreH11 : (q_pre <= (k_pre - 1 ))) (PreH12 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH13 : ((-1) <= old_best)) (PreH14 : (old_best <= n_pre)) (PreH15 : (0 <= add_pre)) (PreH16 : (add_pre <= 1)) (PreH17 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((( &( "c" ) )) # Int64  |->_)
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((k_pre - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (k_pre - x_pre )) ”
.

Definition check_safety_wit_3 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) <> (INT64_MIN)) \/ (q_pre <> (-1))) ” 
  &&  “ (q_pre <> 0) ”
.

Definition check_safety_wit_4 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((((k_pre - x_pre ) + add_pre ) - 1 ) <> (INT64_MIN)) \/ (q_pre <> (-1))) ” 
  &&  “ (q_pre <> 0) ”
.

Definition check_safety_wit_5 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) - 1 )) ”
.

Definition check_safety_wit_6 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_7 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH2 : (add_pre <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) - x_pre )) ”
.

Definition check_safety_wit_8 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH2 : (add_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) - x_pre )) ”
.

Definition check_safety_wit_9 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_10 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre = 0)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH3 : (add_pre <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= x_pre)) (PreH7 : (x_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (n_pre <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= (2 * n_pre ))) (PreH13 : (0 <= q_pre)) (PreH14 : (q_pre <= (k_pre - 1 ))) (PreH15 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH16 : ((-1) <= old_best)) (PreH17 : (old_best <= n_pre)) (PreH18 : (0 <= add_pre)) (PreH19 : (add_pre <= 1)) (PreH20 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH21 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ False ”
.

Definition check_safety_wit_11 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (add_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ False ”
.

Definition check_safety_wit_12 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre = 0)) (PreH2 : (add_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_13 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH5 : (add_pre <> 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_14 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH5 : (add_pre <> 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ”
.

Definition check_safety_wit_15 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH5 : (add_pre <> 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_16 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH5 : (add_pre = 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_17 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH5 : (add_pre = 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ”
.

Definition check_safety_wit_18 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH5 : (add_pre = 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_19 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_20 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ”
.

Definition check_safety_wit_21 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_22 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_23 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ”
.

Definition check_safety_wit_24 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_25 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <> (INT64_MIN)) \/ ((q_pre + 1 ) <> (-1))) ” 
  &&  “ ((q_pre + 1 ) <> 0) ”
.

Definition check_safety_wit_26 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_27 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre )) ”
.

Definition check_safety_wit_28 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) )) ”
.

Definition check_safety_wit_29 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition check_safety_wit_30 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_safety_wit_31 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_32 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <> (INT64_MIN)) \/ ((q_pre + 1 ) <> (-1))) ” 
  &&  “ ((q_pre + 1 ) <> 0) ”
.

Definition check_safety_wit_33 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_34 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre )) ”
.

Definition check_safety_wit_35 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) )) ”
.

Definition check_safety_wit_36 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition check_safety_wit_37 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_safety_wit_38 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_39 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <> (INT64_MIN)) \/ ((q_pre + 1 ) <> (-1))) ” 
  &&  “ ((q_pre + 1 ) <> 0) ”
.

Definition check_safety_wit_40 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_41 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre )) ”
.

Definition check_safety_wit_42 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) )) ”
.

Definition check_safety_wit_43 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition check_safety_wit_44 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_safety_wit_45 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_46 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <> (INT64_MIN)) \/ ((q_pre + 1 ) <> (-1))) ” 
  &&  “ ((q_pre + 1 ) <> 0) ”
.

Definition check_safety_wit_47 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((q_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (q_pre + 1 )) ”
.

Definition check_safety_wit_48 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre )) ”
.

Definition check_safety_wit_49 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) )) ”
.

Definition check_safety_wit_50 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition check_safety_wit_51 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_safety_wit_52 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_53 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : (lo <= hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (0 <= add_pre)) (PreH14 : (add_pre <= 1)) (PreH15 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH16 : (L_pre <= lo)) (PreH17 : (hi <= R_pre)) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((( &( "c" ) )) # Int64  |-> c)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((hi - n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (hi - n_pre )) ”
.

Definition check_safety_wit_54 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) > old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((( &( "c" ) )) # Int64  |-> c)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((hi - n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (hi - n_pre )) ”
.

Definition check_entail_wit_1_1 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre <> 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) = ((k_pre - x_pre ) + add_pre )) ” 
  &&  “ (L_pre <= retval) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre retval retval_2 ) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ”
  &&  ((best_pre) # Int64  |-> old_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre <> 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  TT && emp 
|--
  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre retval retval_2 ) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ (L_pre <= retval) ”
  &&  emp
).

Definition check_entail_wit_1_1_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre <> 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre retval retval_2 )
.

Definition check_entail_wit_1_1_split_goal_2 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre <> 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  (retval_2 <= R_pre)
.

Definition check_entail_wit_1_1_split_goal_3 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre <> 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  (L_pre <= retval)
.

Definition check_entail_wit_1_2 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre = 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) = ((k_pre - x_pre ) + add_pre )) ” 
  &&  “ (L_pre <= retval) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre retval retval_2 ) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ”
  &&  ((best_pre) # Int64  |-> old_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre = 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  TT && emp 
|--
  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre 0 retval retval_2 ) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ (L_pre <= retval) ”
  &&  emp
).

Definition check_entail_wit_1_2_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre = 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre 0 retval retval_2 )
.

Definition check_entail_wit_1_2_split_goal_2 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre = 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  (retval_2 <= R_pre)
.

Definition check_entail_wit_1_2_split_goal_3 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult retval_3 (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult retval_5 retval_6 retval )) (PreH3 : (((retval_6 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_6 * (q_pre + 1 ) ))) (PreH5 : (MaxResult L_pre retval_4 retval_5 )) (PreH6 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH7 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH8 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH9 : (add_pre = 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= n_pre)) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 100000000000)) (PreH16 : (n_pre <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= (2 * n_pre ))) (PreH19 : (0 <= q_pre)) (PreH20 : (q_pre <= (k_pre - 1 ))) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : ((-1) <= old_best)) (PreH23 : (old_best <= n_pre)) (PreH24 : (0 <= add_pre)) (PreH25 : (add_pre <= 1)) (PreH26 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH27 : (q_pre <> 0)) ,
  (L_pre <= retval)
.

Definition check_entail_wit_1_3 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH7 : (add_pre = 0)) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) = ((k_pre - x_pre ) + add_pre )) ” 
  &&  “ (L_pre <= retval) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre retval retval_2 ) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ”
  &&  ((best_pre) # Int64  |-> old_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH7 : (add_pre = 0)) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  TT && emp 
|--
  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre 0 0 retval retval_2 ) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ (L_pre <= retval) ”
  &&  emp
).

Definition check_entail_wit_1_3_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH7 : (add_pre = 0)) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre 0 0 retval retval_2 )
.

Definition check_entail_wit_1_3_split_goal_2 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH7 : (add_pre = 0)) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  (retval_2 <= R_pre)
.

Definition check_entail_wit_1_3_split_goal_3 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH7 : (add_pre = 0)) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  (L_pre <= retval)
.

Definition check_entail_wit_1_4 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (add_pre <> 0)) (PreH7 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) = ((k_pre - x_pre ) + add_pre )) ” 
  &&  “ (L_pre <= retval) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre retval retval_2 ) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ”
  &&  ((best_pre) # Int64  |-> old_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (add_pre <> 0)) (PreH7 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  TT && emp 
|--
  “ (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre 0 add_pre retval retval_2 ) ” 
  &&  “ (retval_2 <= R_pre) ” 
  &&  “ (L_pre <= retval) ”
  &&  emp
).

Definition check_entail_wit_1_4_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (add_pre <> 0)) (PreH7 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre 0 add_pre retval retval_2 )
.

Definition check_entail_wit_1_4_split_goal_2 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (add_pre <> 0)) (PreH7 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  (retval_2 <= R_pre)
.

Definition check_entail_wit_1_4_split_goal_3 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval: Z) (retval_2: Z) (PreH1 : (MinResult R_pre (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) retval_2 )) (PreH2 : (MaxResult L_pre retval_3 retval )) (PreH3 : (((retval_3 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH4 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_3 * (q_pre + 1 ) ))) (PreH5 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH6 : (add_pre <> 0)) (PreH7 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre = 0)) ,
  (L_pre <= retval)
.

Definition check_return_wit_1 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) < 0)) (PreH2 : (add_pre = 0)) (PreH3 : (add_pre = 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= x_pre)) (PreH7 : (x_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (n_pre <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= (2 * n_pre ))) (PreH13 : (0 <= q_pre)) (PreH14 : (q_pre <= (k_pre - 1 ))) (PreH15 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH16 : ((-1) <= old_best)) (PreH17 : (old_best <= n_pre)) (PreH18 : (0 <= add_pre)) (PreH19 : (add_pre <= 1)) (PreH20 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH21 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) < 0)) (PreH2 : (add_pre = 0)) (PreH3 : (add_pre = 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= x_pre)) (PreH7 : (x_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (n_pre <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= (2 * n_pre ))) (PreH13 : (0 <= q_pre)) (PreH14 : (q_pre <= (k_pre - 1 ))) (PreH15 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH16 : ((-1) <= old_best)) (PreH17 : (old_best <= n_pre)) (PreH18 : (0 <= add_pre)) (PreH19 : (add_pre <= 1)) (PreH20 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH21 : (q_pre = 0)) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (0 + 1 ) old_best ) ”
  &&  emp
).

Definition check_return_wit_1_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) < 0)) (PreH2 : (add_pre = 0)) (PreH3 : (add_pre = 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= x_pre)) (PreH7 : (x_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (n_pre <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= (2 * n_pre ))) (PreH13 : (0 <= q_pre)) (PreH14 : (q_pre <= (k_pre - 1 ))) (PreH15 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH16 : ((-1) <= old_best)) (PreH17 : (old_best <= n_pre)) (PreH18 : (0 <= add_pre)) (PreH19 : (add_pre <= 1)) (PreH20 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH21 : (q_pre = 0)) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (0 + 1 ) old_best )
.

Definition check_return_wit_2 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) < 1)) (PreH2 : (add_pre <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) < 1)) (PreH2 : (add_pre <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre = 0)) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best ) ”
  &&  emp
).

Definition check_return_wit_2_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) < 1)) (PreH2 : (add_pre <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre = 0)) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best )
.

Definition check_return_wit_3 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) > x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) > x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (0 + 1 ) old_best ) ”
  &&  emp
).

Definition check_return_wit_3_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) > x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (0 + 1 ) old_best )
.

Definition check_return_wit_4 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) > x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) > x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best ) ”
  &&  emp
).

Definition check_return_wit_4_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) > x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best )
.

Definition check_return_wit_5 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) > old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((best_pre) # Int64  |-> (hi - n_pre ))
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) > old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) (hi - n_pre ) ) ”
  &&  emp
).

Definition check_return_wit_5_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) > old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) (hi - n_pre ) )
.

Definition check_return_wit_6 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : (lo > hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (0 <= add_pre)) (PreH14 : (add_pre <= 1)) (PreH15 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH16 : (L_pre <= lo)) (PreH17 : (hi <= R_pre)) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((best_pre) # Int64  |-> old_best)
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : (lo > hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (0 <= add_pre)) (PreH14 : (add_pre <= 1)) (PreH15 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH16 : (L_pre <= lo)) (PreH17 : (hi <= R_pre)) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best ) ”
  &&  emp
).

Definition check_return_wit_6_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : (lo > hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (0 <= add_pre)) (PreH14 : (add_pre <= 1)) (PreH15 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH16 : (L_pre <= lo)) (PreH17 : (hi <= R_pre)) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best )
.

Definition check_return_wit_7 := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) <= old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  ((best_pre) # Int64  |-> old_best)
|--
  EX (new_best: Z) ,
  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) new_best ) ”
  &&  ((best_pre) # Int64  |-> new_best)
) \/
(
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) <= old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best ) ”
  &&  emp
).

Definition check_return_wit_7_split_goal_1 := 
forall (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (c: Z) (lo: Z) (hi: Z) (PreH1 : ((hi - n_pre ) <= old_best)) (PreH2 : (lo <= hi)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (0 <= add_pre)) (PreH15 : (add_pre <= 1)) (PreH16 : (c = ((k_pre - x_pre ) + add_pre ))) (PreH17 : (L_pre <= lo)) (PreH18 : (hi <= R_pre)) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH22 : (CandyFeasibleInterval n_pre x_pre k_pre L_pre R_pre q_pre add_pre lo hi )) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) ,
  (CandySearchBlock n_pre x_pre k_pre L_pre R_pre (add_pre + 1 ) old_best )
.

Definition check_partial_solve_wit_1_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ (((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre )) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre <> 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre )) ” 
  &&  “ (((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) <= 1000000000000) ”
).

Definition check_partial_solve_wit_1_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre <> 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre )) ”
.

Definition check_partial_solve_wit_1_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre <> 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_1_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ (((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre )) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_1 := check_partial_solve_wit_1_pure -> check_partial_solve_wit_1_aux.

Definition check_partial_solve_wit_2_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) ÷ q_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((((k_pre - x_pre ) + 0 ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((k_pre - x_pre ) + 0 ) ÷ q_pre )) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre = 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + 0 ) ÷ q_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + 0 ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((((k_pre - x_pre ) + 0 ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((k_pre - x_pre ) + 0 ) ÷ q_pre )) ”
).

Definition check_partial_solve_wit_2_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre = 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + 0 ) ÷ q_pre )) ”
.

Definition check_partial_solve_wit_2_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre = 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + 0 ) ÷ q_pre ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_2_pure_split_goal_3 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre = 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((k_pre - x_pre ) + 0 ) ÷ q_pre ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_2_pure_split_goal_4 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (R_pre <= INT64_MAX)) (PreH10 : (old_best >= INT64_MIN)) (PreH11 : (add_pre >= INT64_MIN)) (PreH12 : (k_pre >= INT64_MIN)) (PreH13 : (x_pre >= INT64_MIN)) (PreH14 : (n_pre >= INT64_MIN)) (PreH15 : (q_pre >= INT64_MIN)) (PreH16 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (add_pre = 0)) (PreH20 : (1 <= n_pre)) (PreH21 : (n_pre <= 100000000000)) (PreH22 : (1 <= x_pre)) (PreH23 : (x_pre <= n_pre)) (PreH24 : (1 <= k_pre)) (PreH25 : (k_pre <= 100000000000)) (PreH26 : (n_pre <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= (2 * n_pre ))) (PreH29 : (0 <= q_pre)) (PreH30 : (q_pre <= (k_pre - 1 ))) (PreH31 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH32 : ((-1) <= old_best)) (PreH33 : (old_best <= n_pre)) (PreH34 : (0 <= add_pre)) (PreH35 : (add_pre <= 1)) (PreH36 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH37 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + 0 ) ÷ q_pre )) ”
.

Definition check_partial_solve_wit_2_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (add_pre = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (n_pre <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= (2 * n_pre ))) (PreH11 : (0 <= q_pre)) (PreH12 : (q_pre <= (k_pre - 1 ))) (PreH13 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH14 : ((-1) <= old_best)) (PreH15 : (old_best <= n_pre)) (PreH16 : (0 <= add_pre)) (PreH17 : (add_pre <= 1)) (PreH18 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH19 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) ÷ q_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((((k_pre - x_pre ) + 0 ) ÷ q_pre ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((k_pre - x_pre ) + 0 ) ÷ q_pre )) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_2 := check_partial_solve_wit_2_pure -> check_partial_solve_wit_2_aux.

Definition check_partial_solve_wit_3_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH2 : (add_pre <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= 1000000000000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000000000) ”
.

Definition check_partial_solve_wit_3_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH2 : (add_pre <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= 1000000000000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000000000) ” 
  &&  “ (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval ) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_3 := check_partial_solve_wit_3_pure -> check_partial_solve_wit_3_aux.

Definition check_partial_solve_wit_4_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_2: Z) (retval: Z) (PreH1 : (((retval - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval * q_pre ))) (PreH3 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_2 )) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_2)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_4_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_2: Z) (retval: Z) (PreH1 : (((retval - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval * q_pre ))) (PreH3 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_2 )) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ (((retval - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval * q_pre )) ” 
  &&  “ (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_2 ) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_4 := check_partial_solve_wit_4_pure -> check_partial_solve_wit_4_aux.

Definition check_partial_solve_wit_5_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH2 : (add_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= 1000000000000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000000000) ”
.

Definition check_partial_solve_wit_5_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH2 : (add_pre = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (n_pre <= L_pre)) (PreH10 : (L_pre <= R_pre)) (PreH11 : (R_pre <= (2 * n_pre ))) (PreH12 : (0 <= q_pre)) (PreH13 : (q_pre <= (k_pre - 1 ))) (PreH14 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH15 : ((-1) <= old_best)) (PreH16 : (old_best <= n_pre)) (PreH17 : (0 <= add_pre)) (PreH18 : (add_pre <= 1)) (PreH19 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH20 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= 1000000000000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000000000) ” 
  &&  “ (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval ) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_5 := check_partial_solve_wit_5_pure -> check_partial_solve_wit_5_aux.

Definition check_partial_solve_wit_6_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_2: Z) (retval: Z) (PreH1 : (((retval - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval * q_pre ))) (PreH3 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_2 )) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_2)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_6_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_2: Z) (retval: Z) (PreH1 : (((retval - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval * q_pre ))) (PreH3 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_2 )) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ (((retval - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval * q_pre )) ” 
  &&  “ (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_2 ) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_6 := check_partial_solve_wit_6_pure -> check_partial_solve_wit_6_aux.

Definition check_partial_solve_wit_7_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH5 : (add_pre <> 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_7_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH5 : (add_pre <> 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ” 
  &&  “ (MaxResult L_pre retval_2 retval_3 ) ” 
  &&  “ (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre )) ” 
  &&  “ (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval ) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_7 := check_partial_solve_wit_7_pure -> check_partial_solve_wit_7_aux.

Definition check_partial_solve_wit_8_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH3 : (MaxResult L_pre retval_4 retval )) (PreH4 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH5 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH6 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval_2) ” 
  &&  “ (retval_2 <= 1000000000000) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval <= INT64_MAX)) (PreH11 : (retval_3 <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval >= INT64_MIN)) (PreH22 : (retval_3 >= INT64_MIN)) (PreH23 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH24 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH25 : (MaxResult L_pre retval_4 retval )) (PreH26 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH27 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH28 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH29 : (add_pre <> 0)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 100000000000)) (PreH32 : (1 <= x_pre)) (PreH33 : (x_pre <= n_pre)) (PreH34 : (1 <= k_pre)) (PreH35 : (k_pre <= 100000000000)) (PreH36 : (n_pre <= L_pre)) (PreH37 : (L_pre <= R_pre)) (PreH38 : (R_pre <= (2 * n_pre ))) (PreH39 : (0 <= q_pre)) (PreH40 : (q_pre <= (k_pre - 1 ))) (PreH41 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH42 : ((-1) <= old_best)) (PreH43 : (old_best <= n_pre)) (PreH44 : (0 <= add_pre)) (PreH45 : (add_pre <= 1)) (PreH46 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH47 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ”
).

Definition check_partial_solve_wit_8_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval <= INT64_MAX)) (PreH11 : (retval_3 <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval >= INT64_MIN)) (PreH22 : (retval_3 >= INT64_MIN)) (PreH23 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH24 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH25 : (MaxResult L_pre retval_4 retval )) (PreH26 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH27 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH28 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH29 : (add_pre <> 0)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 100000000000)) (PreH32 : (1 <= x_pre)) (PreH33 : (x_pre <= n_pre)) (PreH34 : (1 <= k_pre)) (PreH35 : (k_pre <= 100000000000)) (PreH36 : (n_pre <= L_pre)) (PreH37 : (L_pre <= R_pre)) (PreH38 : (R_pre <= (2 * n_pre ))) (PreH39 : (0 <= q_pre)) (PreH40 : (q_pre <= (k_pre - 1 ))) (PreH41 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH42 : ((-1) <= old_best)) (PreH43 : (old_best <= n_pre)) (PreH44 : (0 <= add_pre)) (PreH45 : (add_pre <= 1)) (PreH46 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH47 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ”
.

Definition check_partial_solve_wit_8_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval <= INT64_MAX)) (PreH11 : (retval_3 <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval >= INT64_MIN)) (PreH22 : (retval_3 >= INT64_MIN)) (PreH23 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH24 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH25 : (MaxResult L_pre retval_4 retval )) (PreH26 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH27 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH28 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH29 : (add_pre <> 0)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 100000000000)) (PreH32 : (1 <= x_pre)) (PreH33 : (x_pre <= n_pre)) (PreH34 : (1 <= k_pre)) (PreH35 : (k_pre <= 100000000000)) (PreH36 : (n_pre <= L_pre)) (PreH37 : (L_pre <= R_pre)) (PreH38 : (R_pre <= (2 * n_pre ))) (PreH39 : (0 <= q_pre)) (PreH40 : (q_pre <= (k_pre - 1 ))) (PreH41 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH42 : ((-1) <= old_best)) (PreH43 : (old_best <= n_pre)) (PreH44 : (0 <= add_pre)) (PreH45 : (add_pre <= 1)) (PreH46 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH47 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_8_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH3 : (MaxResult L_pre retval_4 retval )) (PreH4 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH5 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH6 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 )) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval_2) ” 
  &&  “ (retval_2 <= 1000000000000) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) )) ” 
  &&  “ (MaxResult L_pre retval_4 retval ) ” 
  &&  “ (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre )) ” 
  &&  “ (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval_3 ) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_8 := check_partial_solve_wit_8_pure -> check_partial_solve_wit_8_aux.

Definition check_partial_solve_wit_9_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH5 : (add_pre = 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_3)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_9_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (MaxResult L_pre retval_2 retval_3 )) (PreH2 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH4 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH5 : (add_pre = 0)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= x_pre)) (PreH9 : (x_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 100000000000)) (PreH12 : (n_pre <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= (2 * n_pre ))) (PreH15 : (0 <= q_pre)) (PreH16 : (q_pre <= (k_pre - 1 ))) (PreH17 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH18 : ((-1) <= old_best)) (PreH19 : (old_best <= n_pre)) (PreH20 : (0 <= add_pre)) (PreH21 : (add_pre <= 1)) (PreH22 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH23 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ” 
  &&  “ (MaxResult L_pre retval_2 retval_3 ) ” 
  &&  “ (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre )) ” 
  &&  “ (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval ) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_9 := check_partial_solve_wit_9_pure -> check_partial_solve_wit_9_aux.

Definition check_partial_solve_wit_10_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH3 : (MaxResult L_pre retval_4 retval )) (PreH4 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH5 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH6 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval_2) ” 
  &&  “ (retval_2 <= 1000000000000) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval <= INT64_MAX)) (PreH11 : (retval_3 <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval >= INT64_MIN)) (PreH22 : (retval_3 >= INT64_MIN)) (PreH23 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH24 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH25 : (MaxResult L_pre retval_4 retval )) (PreH26 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH27 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH28 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH29 : (add_pre = 0)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 100000000000)) (PreH32 : (1 <= x_pre)) (PreH33 : (x_pre <= n_pre)) (PreH34 : (1 <= k_pre)) (PreH35 : (k_pre <= 100000000000)) (PreH36 : (n_pre <= L_pre)) (PreH37 : (L_pre <= R_pre)) (PreH38 : (R_pre <= (2 * n_pre ))) (PreH39 : (0 <= q_pre)) (PreH40 : (q_pre <= (k_pre - 1 ))) (PreH41 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH42 : ((-1) <= old_best)) (PreH43 : (old_best <= n_pre)) (PreH44 : (0 <= add_pre)) (PreH45 : (add_pre <= 1)) (PreH46 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH47 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ”
).

Definition check_partial_solve_wit_10_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval <= INT64_MAX)) (PreH11 : (retval_3 <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval >= INT64_MIN)) (PreH22 : (retval_3 >= INT64_MIN)) (PreH23 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH24 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH25 : (MaxResult L_pre retval_4 retval )) (PreH26 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH27 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH28 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH29 : (add_pre = 0)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 100000000000)) (PreH32 : (1 <= x_pre)) (PreH33 : (x_pre <= n_pre)) (PreH34 : (1 <= k_pre)) (PreH35 : (k_pre <= 100000000000)) (PreH36 : (n_pre <= L_pre)) (PreH37 : (L_pre <= R_pre)) (PreH38 : (R_pre <= (2 * n_pre ))) (PreH39 : (0 <= q_pre)) (PreH40 : (q_pre <= (k_pre - 1 ))) (PreH41 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH42 : ((-1) <= old_best)) (PreH43 : (old_best <= n_pre)) (PreH44 : (0 <= add_pre)) (PreH45 : (add_pre <= 1)) (PreH46 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH47 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ”
.

Definition check_partial_solve_wit_10_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval <= INT64_MAX)) (PreH11 : (retval_3 <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval >= INT64_MIN)) (PreH22 : (retval_3 >= INT64_MIN)) (PreH23 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH24 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH25 : (MaxResult L_pre retval_4 retval )) (PreH26 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH27 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH28 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH29 : (add_pre = 0)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 100000000000)) (PreH32 : (1 <= x_pre)) (PreH33 : (x_pre <= n_pre)) (PreH34 : (1 <= k_pre)) (PreH35 : (k_pre <= 100000000000)) (PreH36 : (n_pre <= L_pre)) (PreH37 : (L_pre <= R_pre)) (PreH38 : (R_pre <= (2 * n_pre ))) (PreH39 : (0 <= q_pre)) (PreH40 : (q_pre <= (k_pre - 1 ))) (PreH41 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH42 : ((-1) <= old_best)) (PreH43 : (old_best <= n_pre)) (PreH44 : (0 <= add_pre)) (PreH45 : (add_pre <= 1)) (PreH46 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH47 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval_3)
  **  ((( &( "lo" ) )) # Int64  |-> retval)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_10_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_2: Z) (PreH1 : (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) ))) (PreH3 : (MaxResult L_pre retval_4 retval )) (PreH4 : (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH5 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre ))) (PreH6 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 )) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval_2) ” 
  &&  “ (retval_2 <= 1000000000000) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (((retval_2 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_2 * (q_pre + 1 ) )) ” 
  &&  “ (MaxResult L_pre retval_4 retval ) ” 
  &&  “ (((retval_4 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_4 * q_pre )) ” 
  &&  “ (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval_3 ) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_10 := check_partial_solve_wit_10_pure -> check_partial_solve_wit_10_aux.

Definition check_partial_solve_wit_11_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_11_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH3 : (add_pre = 0)) (PreH4 : (add_pre = 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) <= x_pre) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) >= 0) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre = 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_11 := check_partial_solve_wit_11_pure -> check_partial_solve_wit_11_aux.

Definition check_partial_solve_wit_12_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH3 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH4 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH5 : (add_pre = 0)) (PreH6 : (add_pre = 0)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= x_pre)) (PreH10 : (x_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 100000000000)) (PreH13 : (n_pre <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= (2 * n_pre ))) (PreH16 : (0 <= q_pre)) (PreH17 : (q_pre <= (k_pre - 1 ))) (PreH18 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (0 <= add_pre)) (PreH22 : (add_pre <= 1)) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH24 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_12_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH3 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH4 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH5 : (add_pre = 0)) (PreH6 : (add_pre = 0)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= x_pre)) (PreH10 : (x_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 100000000000)) (PreH13 : (n_pre <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= (2 * n_pre ))) (PreH16 : (0 <= q_pre)) (PreH17 : (q_pre <= (k_pre - 1 ))) (PreH18 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (0 <= add_pre)) (PreH22 : (add_pre <= 1)) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH24 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) )) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) <= x_pre) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) >= 0) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre = 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_12 := check_partial_solve_wit_12_pure -> check_partial_solve_wit_12_aux.

Definition check_partial_solve_wit_13_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_13_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (PreH1 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH2 : (add_pre <> 0)) (PreH3 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH4 : (add_pre <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= x_pre)) (PreH8 : (x_pre <= n_pre)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (n_pre <= L_pre)) (PreH12 : (L_pre <= R_pre)) (PreH13 : (R_pre <= (2 * n_pre ))) (PreH14 : (0 <= q_pre)) (PreH15 : (q_pre <= (k_pre - 1 ))) (PreH16 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH17 : ((-1) <= old_best)) (PreH18 : (old_best <= n_pre)) (PreH19 : (0 <= add_pre)) (PreH20 : (add_pre <= 1)) (PreH21 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH22 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= 1000000000000) ” 
  &&  “ (1 <= (q_pre + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= 1000000000000) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) <= x_pre) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) >= 1) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre = 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_13 := check_partial_solve_wit_13_pure -> check_partial_solve_wit_13_aux.

Definition check_partial_solve_wit_14_pure := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH3 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH4 : (add_pre <> 0)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH6 : (add_pre <> 0)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= x_pre)) (PreH10 : (x_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 100000000000)) (PreH13 : (n_pre <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= (2 * n_pre ))) (PreH16 : (0 <= q_pre)) (PreH17 : (q_pre <= (k_pre - 1 ))) (PreH18 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (0 <= add_pre)) (PreH22 : (add_pre <= 1)) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH24 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> L_pre)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_14_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (PreH1 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH2 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH3 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH4 : (add_pre <> 0)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH6 : (add_pre <> 0)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= x_pre)) (PreH10 : (x_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 100000000000)) (PreH13 : (n_pre <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= (2 * n_pre ))) (PreH16 : (0 <= q_pre)) (PreH17 : (q_pre <= (k_pre - 1 ))) (PreH18 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH19 : ((-1) <= old_best)) (PreH20 : (old_best <= n_pre)) (PreH21 : (0 <= add_pre)) (PreH22 : (add_pre <= 1)) (PreH23 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH24 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= L_pre) ” 
  &&  “ (L_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) )) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) <= x_pre) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) >= 1) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre = 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_14 := check_partial_solve_wit_14_pure -> check_partial_solve_wit_14_aux.

Definition check_partial_solve_wit_15_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH30 : (add_pre <> 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ”
).

Definition check_partial_solve_wit_15_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH30 : (add_pre <> 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ”
.

Definition check_partial_solve_wit_15_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH30 : (add_pre <> 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_15_pure_split_goal_3 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH30 : (add_pre <> 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ”
.

Definition check_partial_solve_wit_15_pure_split_goal_4 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH30 : (add_pre <> 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_15_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval )) (PreH8 : (add_pre <> 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (MaxResult retval_3 retval_4 retval_5 ) ” 
  &&  “ (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) )) ” 
  &&  “ (MaxResult L_pre retval_2 retval_3 ) ” 
  &&  “ (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre )) ” 
  &&  “ (MinResult R_pre ((((k_pre - x_pre ) + add_pre ) - 1 ) ÷ q_pre ) retval ) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_15 := check_partial_solve_wit_15_pure -> check_partial_solve_wit_15_aux.

Definition check_partial_solve_wit_16_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ”
).

Definition check_partial_solve_wit_16_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= retval) ”
.

Definition check_partial_solve_wit_16_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ (retval <= 1000000000000) ”
.

Definition check_partial_solve_wit_16_pure_split_goal_3 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ”
.

Definition check_partial_solve_wit_16_pure_split_goal_4 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_16_pure_split_goal_5 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_16_pure_split_goal_6 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (R_pre <= INT64_MAX)) (PreH8 : (L_pre <= INT64_MAX)) (PreH9 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH10 : (retval_5 <= INT64_MAX)) (PreH11 : (retval <= INT64_MAX)) (PreH12 : (old_best >= INT64_MIN)) (PreH13 : (add_pre >= INT64_MIN)) (PreH14 : (k_pre >= INT64_MIN)) (PreH15 : (x_pre >= INT64_MIN)) (PreH16 : (n_pre >= INT64_MIN)) (PreH17 : (q_pre >= INT64_MIN)) (PreH18 : (R_pre >= INT64_MIN)) (PreH19 : (L_pre >= INT64_MIN)) (PreH20 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH21 : (retval_5 >= INT64_MIN)) (PreH22 : (retval >= INT64_MIN)) (PreH23 : (MaxResult retval_3 retval_4 retval_5 )) (PreH24 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH25 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH26 : (MaxResult L_pre retval_2 retval_3 )) (PreH27 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH28 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH29 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH30 : (add_pre = 0)) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 100000000000)) (PreH33 : (1 <= x_pre)) (PreH34 : (x_pre <= n_pre)) (PreH35 : (1 <= k_pre)) (PreH36 : (k_pre <= 100000000000)) (PreH37 : (n_pre <= L_pre)) (PreH38 : (L_pre <= R_pre)) (PreH39 : (R_pre <= (2 * n_pre ))) (PreH40 : (0 <= q_pre)) (PreH41 : (q_pre <= (k_pre - 1 ))) (PreH42 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH43 : ((-1) <= old_best)) (PreH44 : (old_best <= n_pre)) (PreH45 : (0 <= add_pre)) (PreH46 : (add_pre <= 1)) (PreH47 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH48 : (q_pre <> 0)) ,
  ((( &( "hi" ) )) # Int64  |-> retval)
  **  ((( &( "lo" ) )) # Int64  |-> retval_5)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ”
.

Definition check_partial_solve_wit_16_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (MaxResult retval_3 retval_4 retval_5 )) (PreH2 : (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) ))) (PreH4 : (MaxResult L_pre retval_2 retval_3 )) (PreH5 : (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre ))) (PreH6 : ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre ))) (PreH7 : (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval )) (PreH8 : (add_pre = 0)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000000000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (k_pre <= 100000000000)) (PreH15 : (n_pre <= L_pre)) (PreH16 : (L_pre <= R_pre)) (PreH17 : (R_pre <= (2 * n_pre ))) (PreH18 : (0 <= q_pre)) (PreH19 : (q_pre <= (k_pre - 1 ))) (PreH20 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH21 : ((-1) <= old_best)) (PreH22 : (old_best <= n_pre)) (PreH23 : (0 <= add_pre)) (PreH24 : (add_pre <= 1)) (PreH25 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH26 : (q_pre <> 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ (retval <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= retval) ” 
  &&  “ (MaxResult retval_3 retval_4 retval_5 ) ” 
  &&  “ (((retval_4 - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval_4 * (q_pre + 1 ) )) ” 
  &&  “ (MaxResult L_pre retval_2 retval_3 ) ” 
  &&  “ (((retval_2 - 1 ) * q_pre ) < (((k_pre - x_pre ) + add_pre ) - x_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) - x_pre ) <= (retval_2 * q_pre )) ” 
  &&  “ (MinResult R_pre (((k_pre - x_pre ) + add_pre ) ÷ q_pre ) retval ) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre <> 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_16 := check_partial_solve_wit_16_pure -> check_partial_solve_wit_16_aux.

Definition check_partial_solve_wit_17_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH26 : (add_pre = 0)) (PreH27 : (add_pre = 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
).

Definition check_partial_solve_wit_17_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH26 : (add_pre = 0)) (PreH27 : (add_pre = 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
.

Definition check_partial_solve_wit_17_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH26 : (add_pre = 0)) (PreH27 : (add_pre = 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_17_pure_split_goal_3 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH26 : (add_pre = 0)) (PreH27 : (add_pre = 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_17_pure_split_goal_4 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH26 : (add_pre = 0)) (PreH27 : (add_pre = 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
.

Definition check_partial_solve_wit_17_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (((k_pre - x_pre ) + add_pre ) >= 0)) (PreH6 : (add_pre = 0)) (PreH7 : (add_pre = 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + 0 ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ” 
  &&  “ (MaxResult L_pre retval retval_2 ) ” 
  &&  “ (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) )) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) <= x_pre) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) >= 0) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (add_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre = 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_17 := check_partial_solve_wit_17_pure -> check_partial_solve_wit_17_aux.

Definition check_partial_solve_wit_18_pure := 
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
) \/
(
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (add_pre <> 0)) (PreH26 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH27 : (add_pre <> 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
).

Definition check_partial_solve_wit_18_pure_split_goal_1 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (add_pre <> 0)) (PreH26 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH27 : (add_pre <> 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
.

Definition check_partial_solve_wit_18_pure_split_goal_2 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (add_pre <> 0)) (PreH26 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH27 : (add_pre <> 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_18_pure_split_goal_3 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (add_pre <> 0)) (PreH26 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH27 : (add_pre <> 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ”
.

Definition check_partial_solve_wit_18_pure_split_goal_4 := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_best <= INT64_MAX)) (PreH2 : (add_pre <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (n_pre <= INT64_MAX)) (PreH6 : (q_pre <= INT64_MAX)) (PreH7 : (L_pre <= INT64_MAX)) (PreH8 : (((k_pre - x_pre ) + add_pre ) <= INT64_MAX)) (PreH9 : (retval_2 <= INT64_MAX)) (PreH10 : (R_pre <= INT64_MAX)) (PreH11 : (old_best >= INT64_MIN)) (PreH12 : (add_pre >= INT64_MIN)) (PreH13 : (k_pre >= INT64_MIN)) (PreH14 : (x_pre >= INT64_MIN)) (PreH15 : (n_pre >= INT64_MIN)) (PreH16 : (q_pre >= INT64_MIN)) (PreH17 : (L_pre >= INT64_MIN)) (PreH18 : (((k_pre - x_pre ) + add_pre ) >= INT64_MIN)) (PreH19 : (retval_2 >= INT64_MIN)) (PreH20 : (R_pre >= INT64_MIN)) (PreH21 : (MaxResult L_pre retval retval_2 )) (PreH22 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH23 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH24 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH25 : (add_pre <> 0)) (PreH26 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH27 : (add_pre <> 0)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 100000000000)) (PreH30 : (1 <= x_pre)) (PreH31 : (x_pre <= n_pre)) (PreH32 : (1 <= k_pre)) (PreH33 : (k_pre <= 100000000000)) (PreH34 : (n_pre <= L_pre)) (PreH35 : (L_pre <= R_pre)) (PreH36 : (R_pre <= (2 * n_pre ))) (PreH37 : (0 <= q_pre)) (PreH38 : (q_pre <= (k_pre - 1 ))) (PreH39 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH40 : ((-1) <= old_best)) (PreH41 : (old_best <= n_pre)) (PreH42 : (0 <= add_pre)) (PreH43 : (add_pre <= 1)) (PreH44 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH45 : (q_pre = 0)) ,
  ((( &( "hi" ) )) # Int64  |-> R_pre)
  **  ((( &( "lo" ) )) # Int64  |-> retval_2)
  **  ((( &( "c" ) )) # Int64  |-> ((k_pre - x_pre ) + add_pre ))
  **  ((( &( "L" ) )) # Int64  |-> L_pre)
  **  ((( &( "R" ) )) # Int64  |-> R_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "add" ) )) # Int64  |-> add_pre)
  **  ((( &( "best" ) )) # Ptr  |-> best_pre)
  **  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ”
.

Definition check_partial_solve_wit_18_aux := 
forall (best_pre: Z) (add_pre: Z) (k_pre: Z) (x_pre: Z) (n_pre: Z) (q_pre: Z) (R_pre: Z) (L_pre: Z) (old_best: Z) (retval: Z) (retval_2: Z) (PreH1 : (MaxResult L_pre retval retval_2 )) (PreH2 : (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre ))) (PreH3 : ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) ))) (PreH4 : (((k_pre - x_pre ) + add_pre ) <= x_pre)) (PreH5 : (add_pre <> 0)) (PreH6 : (((k_pre - x_pre ) + add_pre ) >= 1)) (PreH7 : (add_pre <> 0)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000000000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= n_pre)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (n_pre <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= (2 * n_pre ))) (PreH17 : (0 <= q_pre)) (PreH18 : (q_pre <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre L_pre R_pre q_pre )) (PreH20 : ((-1) <= old_best)) (PreH21 : (old_best <= n_pre)) (PreH22 : (0 <= add_pre)) (PreH23 : (add_pre <= 1)) (PreH24 : (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best )) (PreH25 : (q_pre = 0)) ,
  ((best_pre) # Int64  |-> old_best)
|--
  “ ((-1000000000000) <= R_pre) ” 
  &&  “ (R_pre <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) )) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (q_pre + 1 ) ) <= 1000000000000) ” 
  &&  “ ((((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) ) <= 1000000000000) ” 
  &&  “ ((-1000000000000) <= (((((k_pre - x_pre ) + add_pre ) + (2 * n_pre ) ) - x_pre ) ÷ (0 + 1 ) )) ” 
  &&  “ (MaxResult L_pre retval retval_2 ) ” 
  &&  “ (((retval - 1 ) * (q_pre + 1 ) ) < (((k_pre - x_pre ) + add_pre ) + n_pre )) ” 
  &&  “ ((((k_pre - x_pre ) + add_pre ) + n_pre ) <= (retval * (q_pre + 1 ) )) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) <= x_pre) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (((k_pre - x_pre ) + add_pre ) >= 1) ” 
  &&  “ (add_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= (2 * n_pre )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (q_pre <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre L_pre R_pre q_pre ) ” 
  &&  “ ((-1) <= old_best) ” 
  &&  “ (old_best <= n_pre) ” 
  &&  “ (0 <= add_pre) ” 
  &&  “ (add_pre <= 1) ” 
  &&  “ (CandySearchBlock n_pre x_pre k_pre L_pre R_pre add_pre old_best ) ” 
  &&  “ (q_pre = 0) ”
  &&  ((best_pre) # Int64  |-> old_best)
.

Definition check_partial_solve_wit_18 := check_partial_solve_wit_18_pure -> check_partial_solve_wit_18_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "z" ) )) # Int64  |-> (k_pre - 1 ))
  **  ((( &( "x" ) )) # Int64  |-> ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_2 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "z" ) )) # Int64  |-> (k_pre - 1 ))
  **  ((( &( "x" ) )) # Int64  |-> ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "z" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int64  |-> ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ ((k_pre - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (k_pre - 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "z" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int64  |-> ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ”
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ”
).

Definition solver_safety_wit_5_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_5_split_goal_2 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ ((INT64_MIN) <= ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ ((((r_pre - l_pre ) + n_pre ) <> (INT64_MIN)) \/ (n_pre <> (-1))) ” 
  &&  “ (n_pre <> 0) ”
.

Definition solver_safety_wit_7 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (((r_pre - l_pre ) + n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((r_pre - l_pre ) + n_pre )) ”
.

Definition solver_safety_wit_8 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ ((r_pre - l_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (r_pre - l_pre )) ”
.

Definition solver_safety_wit_9 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 100000000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= n_pre)) (PreH9 : (1 <= r_pre)) (PreH10 : (r_pre <= n_pre)) (PreH11 : (1 <= x)) (PreH12 : (x <= n_pre)) (PreH13 : (n_pre <= cur)) (PreH14 : (cur <= (2 * n_pre ))) (PreH15 : ((-1) <= best)) (PreH16 : (best <= n_pre)) (PreH17 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_11 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 100000000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= n_pre)) (PreH9 : (1 <= r_pre)) (PreH10 : (r_pre <= n_pre)) (PreH11 : (1 <= x)) (PreH12 : (x <= n_pre)) (PreH13 : (n_pre <= cur)) (PreH14 : (cur <= (2 * n_pre ))) (PreH15 : ((-1) <= best)) (PreH16 : (best <= n_pre)) (PreH17 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_12 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : (cur > (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= (2 * n_pre ))) (PreH16 : ((-1) <= best)) (PreH17 : (best <= n_pre)) (PreH18 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_13 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) <> 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |->_)
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((z <> (INT64_MIN)) \/ ((z ÷ cur ) <> (-1))) ” 
  &&  “ ((z ÷ cur ) <> 0) ”
.

Definition solver_safety_wit_14 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) = 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |->_)
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_15 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) = 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |->_)
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : (cur <= (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= (2 * n_pre ))) (PreH16 : ((-1) <= best)) (PreH17 : (best <= n_pre)) (PreH18 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "q" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((z <> (INT64_MIN)) \/ (cur <> (-1))) ” 
  &&  “ (cur <> 0) ”
.

Definition solver_safety_wit_17 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) = 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (2 * n_pre ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_18 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) <> 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (z ÷ (z ÷ cur ) ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_19 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) <> 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (z ÷ (z ÷ cur ) ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_20 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ cur ) = 0)) (PreH2 : (cur <= (2 * n_pre ))) (PreH3 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH4 : (z = (k_pre - 1 ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000000000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100000000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= n_pre)) (PreH11 : (1 <= r_pre)) (PreH12 : (r_pre <= n_pre)) (PreH13 : (1 <= x)) (PreH14 : (x <= n_pre)) (PreH15 : (n_pre <= cur)) (PreH16 : (cur <= (2 * n_pre ))) (PreH17 : ((-1) <= best)) (PreH18 : (best <= n_pre)) (PreH19 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (2 * n_pre ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_21 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((2 * n_pre ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) = 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (2 * n_pre ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_22 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (z ÷ (z ÷ cur ) ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_23 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  ((( &( "R" ) )) # Int64  |-> (z ÷ (z ÷ cur ) ))
  **  ((( &( "q" ) )) # Int64  |-> (z ÷ cur ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_24 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (q = (z ÷ cur ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (0 <= q)) (PreH18 : (q <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre cur R q )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (new_best: Z) (PreH1 : ((-1) <= new_best)) (PreH2 : (new_best <= n_pre)) (PreH3 : (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best )) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (q = (z ÷ cur ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (1 <= l_pre)) (PreH12 : (l_pre <= n_pre)) (PreH13 : (1 <= r_pre)) (PreH14 : (r_pre <= n_pre)) (PreH15 : (1 <= x)) (PreH16 : (x <= n_pre)) (PreH17 : (n_pre <= cur)) (PreH18 : (cur <= R)) (PreH19 : (R <= (2 * n_pre ))) (PreH20 : (0 <= q)) (PreH21 : (q <= (k_pre - 1 ))) (PreH22 : (QuotientBlock k_pre cur R q )) (PreH23 : ((-1) <= best)) (PreH24 : (best <= n_pre)) (PreH25 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  ((( &( "best" ) )) # Int64  |-> new_best)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 100000000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= n_pre)) (PreH9 : (1 <= r_pre)) (PreH10 : (r_pre <= n_pre)) (PreH11 : (1 <= x)) (PreH12 : (x <= n_pre)) (PreH13 : (n_pre <= cur)) (PreH14 : (cur <= R)) (PreH15 : (R <= (2 * n_pre ))) (PreH16 : (q = (z ÷ cur ))) (PreH17 : (0 <= q)) (PreH18 : (q <= (k_pre - 1 ))) (PreH19 : ((-1) <= best)) (PreH20 : (best <= n_pre)) (PreH21 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((2 * n_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_27 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 100000000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= n_pre)) (PreH9 : (1 <= r_pre)) (PreH10 : (r_pre <= n_pre)) (PreH11 : (1 <= x)) (PreH12 : (x <= n_pre)) (PreH13 : (n_pre <= cur)) (PreH14 : (cur <= R)) (PreH15 : (R <= (2 * n_pre ))) (PreH16 : (q = (z ÷ cur ))) (PreH17 : (0 <= q)) (PreH18 : (q <= (k_pre - 1 ))) (PreH19 : ((-1) <= best)) (PreH20 : (best <= n_pre)) (PreH21 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_28 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (R <> (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (q = (z ÷ cur ))) (PreH18 : (0 <= q)) (PreH19 : (q <= (k_pre - 1 ))) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((R + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (R + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (R <> (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (q = (z ÷ cur ))) (PreH18 : (0 <= q)) (PreH19 : (q <= (k_pre - 1 ))) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  TT && emp 
|--
  “ (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ ((k_pre - 1 ) = (k_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre <= (2 * n_pre )) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= n_pre) ” 
  &&  “ (CandySearchPrefix n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre n_pre (-1) ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  TT && emp 
|--
  “ (CandySearchPrefix n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre n_pre (-1) ) ” 
  &&  “ (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) <= n_pre) ” 
  &&  “ (1 <= ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  (CandySearchPrefix n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre n_pre (-1) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  (((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) <= n_pre)
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= n_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= n_pre)) ,
  (1 <= ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))
.

Definition solver_entail_wit_2_1 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  TT && emp 
|--
  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ ((z ÷ cur ) = (z ÷ cur )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= (2 * n_pre )) ” 
  &&  “ ((2 * n_pre ) <= (2 * n_pre )) ” 
  &&  “ (0 <= (z ÷ cur )) ” 
  &&  “ ((z ÷ cur ) <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur (2 * n_pre ) (z ÷ cur ) ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur (2 * n_pre ) 0 best ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre cur (2 * n_pre ) 0 best ) ” 
  &&  “ (QuotientBlock k_pre cur (2 * n_pre ) ((k_pre - 1 ) ÷ cur ) ) ” 
  &&  “ (((k_pre - 1 ) ÷ cur ) <= (k_pre - 1 )) ” 
  &&  “ (0 <= ((k_pre - 1 ) ÷ cur )) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (CandySearchBlock n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre cur (2 * n_pre ) 0 best )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (QuotientBlock k_pre cur (2 * n_pre ) ((k_pre - 1 ) ÷ cur ) )
.

Definition solver_entail_wit_2_1_split_goal_3 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (((k_pre - 1 ) ÷ cur ) <= (k_pre - 1 ))
.

Definition solver_entail_wit_2_1_split_goal_4 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) > (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (0 <= ((k_pre - 1 ) ÷ cur ))
.

Definition solver_entail_wit_2_2 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  TT && emp 
|--
  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ ((z ÷ cur ) = (z ÷ cur )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= (z ÷ (z ÷ cur ) )) ” 
  &&  “ ((z ÷ (z ÷ cur ) ) <= (2 * n_pre )) ” 
  &&  “ (0 <= (z ÷ cur )) ” 
  &&  “ ((z ÷ cur ) <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur (z ÷ (z ÷ cur ) ) (z ÷ cur ) ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur (z ÷ (z ÷ cur ) ) 0 best ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre cur ((k_pre - 1 ) ÷ ((k_pre - 1 ) ÷ cur ) ) 0 best ) ” 
  &&  “ (QuotientBlock k_pre cur ((k_pre - 1 ) ÷ ((k_pre - 1 ) ÷ cur ) ) ((k_pre - 1 ) ÷ cur ) ) ” 
  &&  “ (((k_pre - 1 ) ÷ cur ) <= (k_pre - 1 )) ” 
  &&  “ (0 <= ((k_pre - 1 ) ÷ cur )) ” 
  &&  “ (cur <= ((k_pre - 1 ) ÷ ((k_pre - 1 ) ÷ cur ) )) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (CandySearchBlock n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre cur ((k_pre - 1 ) ÷ ((k_pre - 1 ) ÷ cur ) ) 0 best )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (QuotientBlock k_pre cur ((k_pre - 1 ) ÷ ((k_pre - 1 ) ÷ cur ) ) ((k_pre - 1 ) ÷ cur ) )
.

Definition solver_entail_wit_2_2_split_goal_3 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (((k_pre - 1 ) ÷ cur ) <= (k_pre - 1 ))
.

Definition solver_entail_wit_2_2_split_goal_4 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (0 <= ((k_pre - 1 ) ÷ cur ))
.

Definition solver_entail_wit_2_2_split_goal_5 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((z ÷ (z ÷ cur ) ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) <> 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (cur <= ((k_pre - 1 ) ÷ ((k_pre - 1 ) ÷ cur ) ))
.

Definition solver_entail_wit_2_3 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((2 * n_pre ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) = 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  TT && emp 
|--
  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ ((z ÷ cur ) = (z ÷ cur )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= (2 * n_pre )) ” 
  &&  “ ((2 * n_pre ) <= (2 * n_pre )) ” 
  &&  “ (0 <= (z ÷ cur )) ” 
  &&  “ ((z ÷ cur ) <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur (2 * n_pre ) (z ÷ cur ) ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur (2 * n_pre ) 0 best ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((2 * n_pre ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) = 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  TT && emp 
|--
  “ (CandySearchBlock n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre cur (2 * n_pre ) 0 best ) ” 
  &&  “ (QuotientBlock k_pre cur (2 * n_pre ) ((k_pre - 1 ) ÷ cur ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((2 * n_pre ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) = 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (CandySearchBlock n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre cur (2 * n_pre ) 0 best )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (best: Z) (cur: Z) (z: Z) (x: Z) (PreH1 : ((2 * n_pre ) <= (2 * n_pre ))) (PreH2 : ((z ÷ cur ) = 0)) (PreH3 : (cur <= (2 * n_pre ))) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000000000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 100000000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= n_pre)) (PreH12 : (1 <= r_pre)) (PreH13 : (r_pre <= n_pre)) (PreH14 : (1 <= x)) (PreH15 : (x <= n_pre)) (PreH16 : (n_pre <= cur)) (PreH17 : (cur <= (2 * n_pre ))) (PreH18 : ((-1) <= best)) (PreH19 : (best <= n_pre)) (PreH20 : (CandySearchPrefix n_pre x k_pre cur best )) ,
  (QuotientBlock k_pre cur (2 * n_pre ) ((k_pre - 1 ) ÷ cur ) )
.

Definition solver_entail_wit_3 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (new_best_2: Z) (new_best: Z) (PreH1 : ((-1) <= new_best)) (PreH2 : (new_best <= n_pre)) (PreH3 : (CandySearchBlock n_pre x k_pre cur R (1 + 1 ) new_best )) (PreH4 : ((-1) <= new_best_2)) (PreH5 : (new_best_2 <= n_pre)) (PreH6 : (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best_2 )) (PreH7 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH8 : (z = (k_pre - 1 ))) (PreH9 : (q = (z ÷ cur ))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (1 <= l_pre)) (PreH15 : (l_pre <= n_pre)) (PreH16 : (1 <= r_pre)) (PreH17 : (r_pre <= n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= n_pre)) (PreH20 : (n_pre <= cur)) (PreH21 : (cur <= R)) (PreH22 : (R <= (2 * n_pre ))) (PreH23 : (0 <= q)) (PreH24 : (q <= (k_pre - 1 ))) (PreH25 : (QuotientBlock k_pre cur R q )) (PreH26 : ((-1) <= best)) (PreH27 : (best <= n_pre)) (PreH28 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  TT && emp 
|--
  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (q = (z ÷ cur )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchPrefix n_pre x k_pre (R + 1 ) new_best ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (new_best_2: Z) (new_best: Z) (PreH1 : ((-1) <= new_best)) (PreH2 : (new_best <= n_pre)) (PreH3 : (CandySearchBlock n_pre x k_pre cur R (1 + 1 ) new_best )) (PreH4 : ((-1) <= new_best_2)) (PreH5 : (new_best_2 <= n_pre)) (PreH6 : (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best_2 )) (PreH7 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH8 : (z = (k_pre - 1 ))) (PreH9 : (q = (z ÷ cur ))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (1 <= l_pre)) (PreH15 : (l_pre <= n_pre)) (PreH16 : (1 <= r_pre)) (PreH17 : (r_pre <= n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= n_pre)) (PreH20 : (n_pre <= cur)) (PreH21 : (cur <= R)) (PreH22 : (R <= (2 * n_pre ))) (PreH23 : (0 <= q)) (PreH24 : (q <= (k_pre - 1 ))) (PreH25 : (QuotientBlock k_pre cur R q )) (PreH26 : ((-1) <= best)) (PreH27 : (best <= n_pre)) (PreH28 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  TT && emp 
|--
  “ (CandySearchPrefix n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre (R + 1 ) new_best ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (new_best_2: Z) (new_best: Z) (PreH1 : ((-1) <= new_best)) (PreH2 : (new_best <= n_pre)) (PreH3 : (CandySearchBlock n_pre x k_pre cur R (1 + 1 ) new_best )) (PreH4 : ((-1) <= new_best_2)) (PreH5 : (new_best_2 <= n_pre)) (PreH6 : (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best_2 )) (PreH7 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH8 : (z = (k_pre - 1 ))) (PreH9 : (q = (z ÷ cur ))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000000000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 100000000000)) (PreH14 : (1 <= l_pre)) (PreH15 : (l_pre <= n_pre)) (PreH16 : (1 <= r_pre)) (PreH17 : (r_pre <= n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= n_pre)) (PreH20 : (n_pre <= cur)) (PreH21 : (cur <= R)) (PreH22 : (R <= (2 * n_pre ))) (PreH23 : (0 <= q)) (PreH24 : (q <= (k_pre - 1 ))) (PreH25 : (QuotientBlock k_pre cur R q )) (PreH26 : ((-1) <= best)) (PreH27 : (best <= n_pre)) (PreH28 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  (CandySearchPrefix n_pre ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ) k_pre (R + 1 ) new_best )
.

Definition solver_entail_wit_4 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (R <> (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (q = (z ÷ cur ))) (PreH18 : (0 <= q)) (PreH19 : (q <= (k_pre - 1 ))) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  TT && emp 
|--
  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= (R + 1 )) ” 
  &&  “ ((R + 1 ) <= (2 * n_pre )) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (CandySearchPrefix n_pre x k_pre (R + 1 ) best ) ”
  &&  emp
.

Definition solver_return_wit_1 := 
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (R = (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (q = (z ÷ cur ))) (PreH18 : (0 <= q)) (PreH19 : (q <= (k_pre - 1 ))) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  TT && emp 
|--
  “ (Spec n_pre l_pre r_pre k_pre best ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (R = (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (q = (z ÷ cur ))) (PreH18 : (0 <= q)) (PreH19 : (q <= (k_pre - 1 ))) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  TT && emp 
|--
  “ (Spec n_pre l_pre r_pre k_pre best ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (cur: Z) (R: Z) (q: Z) (best: Z) (PreH1 : (R = (2 * n_pre ))) (PreH2 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH3 : (z = (k_pre - 1 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (q = (z ÷ cur ))) (PreH18 : (0 <= q)) (PreH19 : (q <= (k_pre - 1 ))) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchPrefix n_pre x k_pre (R + 1 ) best )) ,
  (Spec n_pre l_pre r_pre k_pre best )
.

Definition solver_partial_solve_wit_1_pure := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (q = (z ÷ cur ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (0 <= q)) (PreH18 : (q <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre cur R q )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur R q ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R 0 best ) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (PreH1 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH2 : (z = (k_pre - 1 ))) (PreH3 : (q = (z ÷ cur ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000000000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100000000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= n_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= n_pre)) (PreH14 : (n_pre <= cur)) (PreH15 : (cur <= R)) (PreH16 : (R <= (2 * n_pre ))) (PreH17 : (0 <= q)) (PreH18 : (q <= (k_pre - 1 ))) (PreH19 : (QuotientBlock k_pre cur R q )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= n_pre)) (PreH22 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur R q ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R 0 best ) ” 
  &&  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ (q = (z ÷ cur )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur R q ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R 0 best ) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (new_best: Z) (PreH1 : ((-1) <= new_best)) (PreH2 : (new_best <= n_pre)) (PreH3 : (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best )) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (q = (z ÷ cur ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (1 <= l_pre)) (PreH12 : (l_pre <= n_pre)) (PreH13 : (1 <= r_pre)) (PreH14 : (r_pre <= n_pre)) (PreH15 : (1 <= x)) (PreH16 : (x <= n_pre)) (PreH17 : (n_pre <= cur)) (PreH18 : (cur <= R)) (PreH19 : (R <= (2 * n_pre ))) (PreH20 : (0 <= q)) (PreH21 : (q <= (k_pre - 1 ))) (PreH22 : (QuotientBlock k_pre cur R q )) (PreH23 : ((-1) <= best)) (PreH24 : (best <= n_pre)) (PreH25 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  ((( &( "best" ) )) # Int64  |-> new_best)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "z" ) )) # Int64  |-> z)
  **  ((( &( "q" ) )) # Int64  |-> q)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  ((( &( "R" ) )) # Int64  |-> R)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur R q ) ” 
  &&  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R 1 new_best ) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (k_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (x: Z) (z: Z) (q: Z) (cur: Z) (R: Z) (best: Z) (new_best: Z) (PreH1 : ((-1) <= new_best)) (PreH2 : (new_best <= n_pre)) (PreH3 : (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best )) (PreH4 : (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 ))) (PreH5 : (z = (k_pre - 1 ))) (PreH6 : (q = (z ÷ cur ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 100000000000)) (PreH11 : (1 <= l_pre)) (PreH12 : (l_pre <= n_pre)) (PreH13 : (1 <= r_pre)) (PreH14 : (r_pre <= n_pre)) (PreH15 : (1 <= x)) (PreH16 : (x <= n_pre)) (PreH17 : (n_pre <= cur)) (PreH18 : (cur <= R)) (PreH19 : (R <= (2 * n_pre ))) (PreH20 : (0 <= q)) (PreH21 : (q <= (k_pre - 1 ))) (PreH22 : (QuotientBlock k_pre cur R q )) (PreH23 : ((-1) <= best)) (PreH24 : (best <= n_pre)) (PreH25 : (CandySearchBlock n_pre x k_pre cur R 0 best )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur R q ) ” 
  &&  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R 1 new_best ) ” 
  &&  “ ((-1) <= new_best) ” 
  &&  “ (new_best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R (0 + 1 ) new_best ) ” 
  &&  “ (x = ((((r_pre - l_pre ) + n_pre ) % ( n_pre ) ) + 1 )) ” 
  &&  “ (z = (k_pre - 1 )) ” 
  &&  “ (q = (z ÷ cur )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= n_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (n_pre <= cur) ” 
  &&  “ (cur <= R) ” 
  &&  “ (R <= (2 * n_pre )) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (k_pre - 1 )) ” 
  &&  “ (QuotientBlock k_pre cur R q ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= n_pre) ” 
  &&  “ (CandySearchBlock n_pre x k_pre cur R 0 best ) ”
  &&  emp
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_maxll_return_wit_1 : maxll_return_wit_1.
Axiom proof_of_maxll_return_wit_2 : maxll_return_wit_2.
Axiom proof_of_minll_return_wit_1 : minll_return_wit_1.
Axiom proof_of_minll_return_wit_2 : minll_return_wit_2.
Axiom proof_of_ceildiv_safety_wit_1 : ceildiv_safety_wit_1.
Axiom proof_of_ceildiv_safety_wit_2 : ceildiv_safety_wit_2.
Axiom proof_of_ceildiv_safety_wit_3 : ceildiv_safety_wit_3.
Axiom proof_of_ceildiv_safety_wit_4 : ceildiv_safety_wit_4.
Axiom proof_of_ceildiv_safety_wit_5 : ceildiv_safety_wit_5.
Axiom proof_of_ceildiv_safety_wit_6 : ceildiv_safety_wit_6.
Axiom proof_of_ceildiv_return_wit_1 : ceildiv_return_wit_1.
Axiom proof_of_ceildiv_return_wit_2 : ceildiv_return_wit_2.
Axiom proof_of_check_safety_wit_1 : check_safety_wit_1.
Axiom proof_of_check_safety_wit_2 : check_safety_wit_2.
Axiom proof_of_check_safety_wit_3 : check_safety_wit_3.
Axiom proof_of_check_safety_wit_4 : check_safety_wit_4.
Axiom proof_of_check_safety_wit_5 : check_safety_wit_5.
Axiom proof_of_check_safety_wit_6 : check_safety_wit_6.
Axiom proof_of_check_safety_wit_7 : check_safety_wit_7.
Axiom proof_of_check_safety_wit_8 : check_safety_wit_8.
Axiom proof_of_check_safety_wit_9 : check_safety_wit_9.
Axiom proof_of_check_safety_wit_10 : check_safety_wit_10.
Axiom proof_of_check_safety_wit_11 : check_safety_wit_11.
Axiom proof_of_check_safety_wit_12 : check_safety_wit_12.
Axiom proof_of_check_safety_wit_13 : check_safety_wit_13.
Axiom proof_of_check_safety_wit_14 : check_safety_wit_14.
Axiom proof_of_check_safety_wit_15 : check_safety_wit_15.
Axiom proof_of_check_safety_wit_16 : check_safety_wit_16.
Axiom proof_of_check_safety_wit_17 : check_safety_wit_17.
Axiom proof_of_check_safety_wit_18 : check_safety_wit_18.
Axiom proof_of_check_safety_wit_19 : check_safety_wit_19.
Axiom proof_of_check_safety_wit_20 : check_safety_wit_20.
Axiom proof_of_check_safety_wit_21 : check_safety_wit_21.
Axiom proof_of_check_safety_wit_22 : check_safety_wit_22.
Axiom proof_of_check_safety_wit_23 : check_safety_wit_23.
Axiom proof_of_check_safety_wit_24 : check_safety_wit_24.
Axiom proof_of_check_safety_wit_25 : check_safety_wit_25.
Axiom proof_of_check_safety_wit_26 : check_safety_wit_26.
Axiom proof_of_check_safety_wit_27 : check_safety_wit_27.
Axiom proof_of_check_safety_wit_28 : check_safety_wit_28.
Axiom proof_of_check_safety_wit_29 : check_safety_wit_29.
Axiom proof_of_check_safety_wit_30 : check_safety_wit_30.
Axiom proof_of_check_safety_wit_31 : check_safety_wit_31.
Axiom proof_of_check_safety_wit_32 : check_safety_wit_32.
Axiom proof_of_check_safety_wit_33 : check_safety_wit_33.
Axiom proof_of_check_safety_wit_34 : check_safety_wit_34.
Axiom proof_of_check_safety_wit_35 : check_safety_wit_35.
Axiom proof_of_check_safety_wit_36 : check_safety_wit_36.
Axiom proof_of_check_safety_wit_37 : check_safety_wit_37.
Axiom proof_of_check_safety_wit_38 : check_safety_wit_38.
Axiom proof_of_check_safety_wit_39 : check_safety_wit_39.
Axiom proof_of_check_safety_wit_40 : check_safety_wit_40.
Axiom proof_of_check_safety_wit_41 : check_safety_wit_41.
Axiom proof_of_check_safety_wit_42 : check_safety_wit_42.
Axiom proof_of_check_safety_wit_43 : check_safety_wit_43.
Axiom proof_of_check_safety_wit_44 : check_safety_wit_44.
Axiom proof_of_check_safety_wit_45 : check_safety_wit_45.
Axiom proof_of_check_safety_wit_46 : check_safety_wit_46.
Axiom proof_of_check_safety_wit_47 : check_safety_wit_47.
Axiom proof_of_check_safety_wit_48 : check_safety_wit_48.
Axiom proof_of_check_safety_wit_49 : check_safety_wit_49.
Axiom proof_of_check_safety_wit_50 : check_safety_wit_50.
Axiom proof_of_check_safety_wit_51 : check_safety_wit_51.
Axiom proof_of_check_safety_wit_52 : check_safety_wit_52.
Axiom proof_of_check_safety_wit_53 : check_safety_wit_53.
Axiom proof_of_check_safety_wit_54 : check_safety_wit_54.
Axiom proof_of_check_entail_wit_1_1 : check_entail_wit_1_1.
Axiom proof_of_check_entail_wit_1_2 : check_entail_wit_1_2.
Axiom proof_of_check_entail_wit_1_3 : check_entail_wit_1_3.
Axiom proof_of_check_entail_wit_1_4 : check_entail_wit_1_4.
Axiom proof_of_check_return_wit_1 : check_return_wit_1.
Axiom proof_of_check_return_wit_2 : check_return_wit_2.
Axiom proof_of_check_return_wit_3 : check_return_wit_3.
Axiom proof_of_check_return_wit_4 : check_return_wit_4.
Axiom proof_of_check_return_wit_5 : check_return_wit_5.
Axiom proof_of_check_return_wit_6 : check_return_wit_6.
Axiom proof_of_check_return_wit_7 : check_return_wit_7.
Axiom proof_of_check_partial_solve_wit_1_pure : check_partial_solve_wit_1_pure.
Axiom proof_of_check_partial_solve_wit_1 : check_partial_solve_wit_1.
Axiom proof_of_check_partial_solve_wit_2_pure : check_partial_solve_wit_2_pure.
Axiom proof_of_check_partial_solve_wit_2 : check_partial_solve_wit_2.
Axiom proof_of_check_partial_solve_wit_3_pure : check_partial_solve_wit_3_pure.
Axiom proof_of_check_partial_solve_wit_3 : check_partial_solve_wit_3.
Axiom proof_of_check_partial_solve_wit_4_pure : check_partial_solve_wit_4_pure.
Axiom proof_of_check_partial_solve_wit_4 : check_partial_solve_wit_4.
Axiom proof_of_check_partial_solve_wit_5_pure : check_partial_solve_wit_5_pure.
Axiom proof_of_check_partial_solve_wit_5 : check_partial_solve_wit_5.
Axiom proof_of_check_partial_solve_wit_6_pure : check_partial_solve_wit_6_pure.
Axiom proof_of_check_partial_solve_wit_6 : check_partial_solve_wit_6.
Axiom proof_of_check_partial_solve_wit_7_pure : check_partial_solve_wit_7_pure.
Axiom proof_of_check_partial_solve_wit_7 : check_partial_solve_wit_7.
Axiom proof_of_check_partial_solve_wit_8_pure : check_partial_solve_wit_8_pure.
Axiom proof_of_check_partial_solve_wit_8 : check_partial_solve_wit_8.
Axiom proof_of_check_partial_solve_wit_9_pure : check_partial_solve_wit_9_pure.
Axiom proof_of_check_partial_solve_wit_9 : check_partial_solve_wit_9.
Axiom proof_of_check_partial_solve_wit_10_pure : check_partial_solve_wit_10_pure.
Axiom proof_of_check_partial_solve_wit_10 : check_partial_solve_wit_10.
Axiom proof_of_check_partial_solve_wit_11_pure : check_partial_solve_wit_11_pure.
Axiom proof_of_check_partial_solve_wit_11 : check_partial_solve_wit_11.
Axiom proof_of_check_partial_solve_wit_12_pure : check_partial_solve_wit_12_pure.
Axiom proof_of_check_partial_solve_wit_12 : check_partial_solve_wit_12.
Axiom proof_of_check_partial_solve_wit_13_pure : check_partial_solve_wit_13_pure.
Axiom proof_of_check_partial_solve_wit_13 : check_partial_solve_wit_13.
Axiom proof_of_check_partial_solve_wit_14_pure : check_partial_solve_wit_14_pure.
Axiom proof_of_check_partial_solve_wit_14 : check_partial_solve_wit_14.
Axiom proof_of_check_partial_solve_wit_15_pure : check_partial_solve_wit_15_pure.
Axiom proof_of_check_partial_solve_wit_15 : check_partial_solve_wit_15.
Axiom proof_of_check_partial_solve_wit_16_pure : check_partial_solve_wit_16_pure.
Axiom proof_of_check_partial_solve_wit_16 : check_partial_solve_wit_16.
Axiom proof_of_check_partial_solve_wit_17_pure : check_partial_solve_wit_17_pure.
Axiom proof_of_check_partial_solve_wit_17 : check_partial_solve_wit_17.
Axiom proof_of_check_partial_solve_wit_18_pure : check_partial_solve_wit_18_pure.
Axiom proof_of_check_partial_solve_wit_18 : check_partial_solve_wit_18.
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
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
