From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  ((( &( "all_and" ) )) # Int  |->_)
  **  ((( &( "all_or" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  ((( &( "all_or" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "all_and" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "all_or" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "all_or" ) )) # Int  |-> (Z.lor all_or (Znth i input 0)))
  **  ((( &( "all_and" ) )) # Int  |-> (Z.land all_and (Znth i input 0)))
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "all_or" ) )) # Int  |-> all_or)
  **  ((( &( "all_and" ) )) # Int  |-> all_and)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ ((all_or - all_and ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (all_or - all_and )) ”
.

Definition solver_entail_wit_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 512) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 1024) ”
  &&  “ (0 <= (Znth 0 input 0)) ”
  &&  “ ((Znth 0 input 0) < 1024) ”
  &&  “ (BitwiseScanState input 0 0 (Znth 0 input 0) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  TT && emp 
|--
  “ (BitwiseScanState input 0 0 (Znth 0 input 0) ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  (BitwiseScanState input 0 0 (Znth 0 input 0) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))
.

Definition solver_entail_wit_2 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 512) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024))) ”
  &&  “ (0 <= (Z.lor all_or (Znth i input 0))) ”
  &&  “ ((Z.lor all_or (Znth i input 0)) < 1024) ”
  &&  “ (0 <= (Z.land all_and (Znth i input 0))) ”
  &&  “ ((Z.land all_and (Znth i input 0)) < 1024) ”
  &&  “ (BitwiseScanState input (i + 1 ) (Z.lor all_or (Znth i input 0)) (Z.land all_and (Znth i input 0)) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  TT && emp 
|--
  “ (BitwiseScanState input (i + 1 ) (Z.lor all_or (Znth i input 0)) (Z.land all_and (Znth i input 0)) ) ”
  &&  “ ((Z.land all_and (Znth i input 0)) < 1024) ”
  &&  “ (0 <= (Z.land all_and (Znth i input 0))) ”
  &&  “ ((Z.lor all_or (Znth i input 0)) < 1024) ”
  &&  “ (0 <= (Z.lor all_or (Znth i input 0))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (BitwiseScanState input (i + 1 ) (Z.lor all_or (Znth i input 0)) (Z.land all_and (Znth i input 0)) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  ((Z.land all_and (Znth i input 0)) < 1024)
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (0 <= (Z.land all_and (Znth i input 0)))
.

Definition solver_entail_wit_2_split_goal_4 :=
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  ((Z.lor all_or (Znth i input 0)) < 1024)
.

Definition solver_entail_wit_2_split_goal_5 :=
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (0 <= (Z.lor all_or (Znth i input 0)))
.

Definition solver_return_wit_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (Spec input (all_or - all_and ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  TT && emp 
|--
  “ (Spec input (all_or - all_and ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (Spec input (all_or - all_and ) )
.

Definition solver_partial_solve_wit_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024)))),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (3 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 512) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input)))) -> ((0 <= (Znth i input 0)) /\ ((Znth i input 0) < 1024))) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 input 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
.

Definition solver_partial_solve_wit_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 512) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024))) ”
  &&  “ (0 <= all_or) ”
  &&  “ (all_or < 1024) ”
  &&  “ (0 <= all_and) ”
  &&  “ (all_and < 1024) ”
  &&  “ (BitwiseScanState input i all_or all_and ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
.

Definition solver_partial_solve_wit_3 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (all_and: Z) (all_or: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024)))) (PreH8 : (0 <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : (0 <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 512) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 1024))) ”
  &&  “ (0 <= all_or) ”
  &&  “ (all_or < 1024) ”
  &&  “ (0 <= all_and) ”
  &&  “ (all_and < 1024) ”
  &&  “ (BitwiseScanState input i all_or all_and ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 512 )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
