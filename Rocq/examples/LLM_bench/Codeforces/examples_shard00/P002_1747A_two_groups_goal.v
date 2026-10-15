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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P002_1747A_two_groups_lib.
Local Open Scope sac.

(*----- Function llabs -----*)

Definition llabs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (x_pre <> (INT64_MIN)) ”
.

Definition llabs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : ((-100000000000000) <= x_pre)) (PreH2 : (x_pre <= 100000000000000)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition llabs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
).

Definition llabs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  ((-x_pre) = (Z.abs (x_pre)))
.

Definition llabs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
).

Definition llabs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-100000000000000) <= x_pre)) (PreH3 : (x_pre <= 100000000000000)) ,
  (x_pre = (Z.abs (x_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-1000000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))) ,
  ((( &( "sum" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-1000000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> (sum + (Znth i input 0) ))
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ ((sum + (Znth i input 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (sum + (Znth i input 0) )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-1000000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))) ,
  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (ListLib.sum ((sublist (0) (0) (input))))) ” 
  &&  “ (((-1000000000) * 0 ) <= 0) ” 
  &&  “ (0 <= (1000000000 * 0 )) ”
  &&  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-1000000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))) ,
  TT && emp 
|--
  “ (0 = (ListLib.sum ((sublist (0) (0) (input))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-1000000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))) ,
  (0 = (ListLib.sum ((sublist (0) (0) (input)))))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-1000000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000000000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))
.

Definition solver_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((sum + (Znth i input 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (input))))) ” 
  &&  “ (((-1000000000) * (i + 1 ) ) <= (sum + (Znth i input 0) )) ” 
  &&  “ ((sum + (Znth i input 0) ) <= (1000000000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  TT && emp 
|--
  “ (((-1000000000) * (i + 1 ) ) <= (sum + (Znth i input 0) )) ” 
  &&  “ ((sum + (Znth i input 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (input))))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  (((-1000000000) * (i + 1 ) ) <= (sum + (Znth i input 0) ))
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  ((sum + (Znth i input 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (input)))))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Z.abs (sum)))) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH10 : (((-1000000000) * i ) <= sum)) (PreH11 : (sum <= (1000000000 * i ))) ,
  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ (Spec input retval ) ”
  &&  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Z.abs (sum)))) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH10 : (((-1000000000) * i ) <= sum)) (PreH11 : (sum <= (1000000000 * i ))) ,
  TT && emp 
|--
  “ (Spec input retval ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Z.abs (sum)))) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH10 : (((-1000000000) * i ) <= sum)) (PreH11 : (sum <= (1000000000 * i ))) ,
  (Spec input retval )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (sum = (ListLib.sum ((sublist (0) (i) (input))))) ” 
  &&  “ (((-1000000000) * i ) <= sum) ” 
  &&  “ (sum <= (1000000000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i input 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
.

Definition solver_partial_solve_wit_2_pure := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ ((-100000000000000) <= sum) ” 
  &&  “ (sum <= 100000000000000) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (sum = (ListLib.sum ((sublist (0) (i) (input)))))) (PreH9 : (((-1000000000) * i ) <= sum)) (PreH10 : (sum <= (1000000000 * i ))) ,
  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
|--
  “ ((-100000000000000) <= sum) ” 
  &&  “ (sum <= 100000000000000) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-1000000000) <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (sum = (ListLib.sum ((sublist (0) (i) (input))))) ” 
  &&  “ (((-1000000000) * i ) <= sum) ” 
  &&  “ (sum <= (1000000000 * i )) ”
  &&  (Int64Array.full a_pre n_pre input )
  **  (Int64Array.undef_seg a_pre n_pre 100005 )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_llabs_safety_wit_1 : llabs_safety_wit_1.
Axiom proof_of_llabs_safety_wit_2 : llabs_safety_wit_2.
Axiom proof_of_llabs_return_wit_1 : llabs_return_wit_1.
Axiom proof_of_llabs_return_wit_2 : llabs_return_wit_2.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
