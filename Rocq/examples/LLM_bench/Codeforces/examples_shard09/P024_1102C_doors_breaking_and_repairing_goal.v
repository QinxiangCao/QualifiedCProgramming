From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P024_1102C_doors_breaking_and_repairing_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  (IntArray.full a_pre n_pre durability )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  (IntArray.full a_pre n_pre durability )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) <= x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ ((cnt + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full a_pre n_pre durability )
|--
  “ (((cnt + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full a_pre n_pre durability )
|--
  “ ((cnt + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full a_pre n_pre durability )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full a_pre n_pre durability )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) <= x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) > x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  (IntArray.full a_pre n_pre durability )
|--
  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= 100000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000))) ”
  &&  “ (n_pre = (Zlength (durability))) ”
  &&  “ (x_pre <= y_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 = (WeakDoorCount (x_pre) ((sublist (0) (0) (durability))))) ”
  &&  (IntArray.full a_pre n_pre durability )
) \/
(
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  TT && emp 
|--
  “ (0 = (WeakDoorCount (x_pre) ((sublist (0) (0) (durability))))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  (0 = (WeakDoorCount (x_pre) ((sublist (0) (0) (durability)))))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))
.

Definition solver_entail_wit_2_1 :=
(
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) <= x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
|--
  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= 100000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000))) ”
  &&  “ (n_pre = (Zlength (durability))) ”
  &&  “ (x_pre <= y_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (cnt + 1 )) ”
  &&  “ ((cnt + 1 ) <= (i + 1 )) ”
  &&  “ ((cnt + 1 ) = (WeakDoorCount (x_pre) ((sublist (0) ((i + 1 )) (durability))))) ”
  &&  (IntArray.full a_pre n_pre durability )
) \/
(
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) <= x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  TT && emp 
|--
  “ ((cnt + 1 ) = (WeakDoorCount (x_pre) ((sublist (0) ((i + 1 )) (durability))))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) <= x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  ((cnt + 1 ) = (WeakDoorCount (x_pre) ((sublist (0) ((i + 1 )) (durability)))))
.

Definition solver_entail_wit_2_2 :=
(
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) > x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
|--
  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= 100000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000))) ”
  &&  “ (n_pre = (Zlength (durability))) ”
  &&  “ (x_pre <= y_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= cnt) ”
  &&  “ (cnt <= (i + 1 )) ”
  &&  “ (cnt = (WeakDoorCount (x_pre) ((sublist (0) ((i + 1 )) (durability))))) ”
  &&  (IntArray.full a_pre n_pre durability )
) \/
(
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) > x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  TT && emp 
|--
  “ (cnt = (WeakDoorCount (x_pre) ((sublist (0) ((i + 1 )) (durability))))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i durability 0) > x_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= y_pre)) (PreH6 : (y_pre <= 100000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH10 : (n_pre = (Zlength (durability)))) (PreH11 : (x_pre <= y_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= i)) (PreH16 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (cnt = (WeakDoorCount (x_pre) ((sublist (0) ((i + 1 )) (durability)))))
.

Definition solver_return_wit_1 :=
(
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
|--
  “ (Spec x_pre y_pre durability ((cnt + 1 ) ÷ 2 ) ) ”
  &&  (IntArray.full a_pre n_pre durability )
) \/
(
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  TT && emp 
|--
  “ (Spec x_pre y_pre durability ((cnt + 1 ) ÷ 2 ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (Spec x_pre y_pre durability ((cnt + 1 ) ÷ 2 ) )
.

Definition solver_return_wit_2 :=
(
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre > y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  (IntArray.full a_pre n_pre durability )
|--
  “ (Spec x_pre y_pre durability n_pre ) ”
  &&  (IntArray.full a_pre n_pre durability )
) \/
(
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre > y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  TT && emp 
|--
  “ (Spec x_pre y_pre durability n_pre ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (durability: (@list Z)) (n_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre > y_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i durability 0)) /\ ((Znth i durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))),
  (Spec x_pre y_pre durability n_pre )
.

Definition solver_partial_solve_wit_1 :=
forall (durability: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (y_pre: Z) (cnt: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= 100000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000)))) (PreH9 : (n_pre = (Zlength (durability)))) (PreH10 : (x_pre <= y_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= i)) (PreH15 : (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability)))))),
  (IntArray.full a_pre n_pre durability )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= 100000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j durability 0)) /\ ((Znth j durability 0) <= 100000))) ”
  &&  “ (n_pre = (Zlength (durability))) ”
  &&  “ (x_pre <= y_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= cnt) ”
  &&  “ (cnt <= i) ”
  &&  “ (cnt = (WeakDoorCount (x_pre) ((sublist (0) (i) (durability))))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i durability 0))
  **  (IntArray.missing_i a_pre i 0 n_pre durability )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
