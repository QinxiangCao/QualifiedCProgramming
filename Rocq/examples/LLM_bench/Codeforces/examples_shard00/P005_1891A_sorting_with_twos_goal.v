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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P005_1891A_sorting_with_twos_lib.
Local Open Scope sac.

(*----- Function is_power_of_two -----*)

Definition is_power_of_two_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 20)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_power_of_two_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 20)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition is_power_of_two_safety_wit_3 := 
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 20)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((x_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre - 1 )) ”
.

Definition is_power_of_two_safety_wit_4 := 
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 20)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_power_of_two_safety_wit_5 := 
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 20)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_power_of_two_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : ((Z.land x_pre (x_pre - 1 )) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 20)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (NonPowerOfTwo x_pre ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : ((Z.land x_pre (x_pre - 1 )) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 20)) ,
  TT && emp 
|--
  “ (NonPowerOfTwo x_pre ) ”
  &&  emp
).

Definition is_power_of_two_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : ((Z.land x_pre (x_pre - 1 )) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 20)) ,
  (NonPowerOfTwo x_pre )
.

Definition is_power_of_two_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : ((Z.land x_pre (x_pre - 1 )) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 20)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (PowerOfTwoPrefix x_pre x_pre ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : ((Z.land x_pre (x_pre - 1 )) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 20)) ,
  TT && emp 
|--
  “ (PowerOfTwoPrefix x_pre x_pre ) ”
  &&  emp
).

Definition is_power_of_two_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : ((Z.land x_pre (x_pre - 1 )) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 20)) ,
  (PowerOfTwoPrefix x_pre x_pre )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 20)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (NonPowerOfTwo i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ False ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (PowerOfTwoPrefix i i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ False ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NonPowerOfTwo i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) input 0) <= (Znth i input 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 20)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (PowerOfTwoPrefix i i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 20)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000)))) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 20) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (SortingWithTwosPrefix input 1 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 20)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000)))) ,
  TT && emp 
|--
  “ (SortingWithTwosPrefix input 1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 20)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000)))) ,
  (SortingWithTwosPrefix input 1 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 20)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) <= 1000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))
.

Definition solver_entail_wit_2_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) input 0) <= (Znth i input 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 20)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 20) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (SortingWithTwosPrefix input (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) input 0) <= (Znth i input 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 20)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (SortingWithTwosPrefix input i )) ,
  TT && emp 
|--
  “ (SortingWithTwosPrefix input (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) input 0) <= (Znth i input 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 20)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (SortingWithTwosPrefix input i )) ,
  (SortingWithTwosPrefix input (i + 1 ) )
.

Definition solver_entail_wit_2_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (PowerOfTwoPrefix i i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 20) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (SortingWithTwosPrefix input (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (PowerOfTwoPrefix i i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  TT && emp 
|--
  “ (SortingWithTwosPrefix input (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (PowerOfTwoPrefix i i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (SortingWithTwosPrefix input (i + 1 ) )
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (Spec input 1 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  TT && emp 
|--
  “ (Spec input 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  (Spec input 1 )
.

Definition solver_return_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NonPowerOfTwo i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (Spec input 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NonPowerOfTwo i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  TT && emp 
|--
  “ (Spec input 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NonPowerOfTwo i )) (PreH4 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH5 : (i < n_pre)) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 20)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SortingWithTwosPrefix input i )) ,
  (Spec input 0 )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 20) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SortingWithTwosPrefix input i ) ”
  &&  (((a_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) input 0))
  **  (IntArray.missing_i a_pre (i - 1 ) 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 20)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 20) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SortingWithTwosPrefix input i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
.

Definition solver_partial_solve_wit_3_pure := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 20)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= 20) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) input 0) > (Znth i input 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 20)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (SortingWithTwosPrefix input i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= 20) ” 
  &&  “ ((Znth (i - 1 ) input 0) > (Znth i input 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 20) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) <= 1000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SortingWithTwosPrefix input i ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 20 )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Module Type VC_Correct.


Axiom proof_of_is_power_of_two_safety_wit_1 : is_power_of_two_safety_wit_1.
Axiom proof_of_is_power_of_two_safety_wit_2 : is_power_of_two_safety_wit_2.
Axiom proof_of_is_power_of_two_safety_wit_3 : is_power_of_two_safety_wit_3.
Axiom proof_of_is_power_of_two_safety_wit_4 : is_power_of_two_safety_wit_4.
Axiom proof_of_is_power_of_two_safety_wit_5 : is_power_of_two_safety_wit_5.
Axiom proof_of_is_power_of_two_return_wit_1 : is_power_of_two_return_wit_1.
Axiom proof_of_is_power_of_two_return_wit_2 : is_power_of_two_return_wit_2.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
