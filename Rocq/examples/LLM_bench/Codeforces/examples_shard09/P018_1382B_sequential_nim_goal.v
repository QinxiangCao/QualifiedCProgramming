From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (IntArray.full a_pre n_pre piles )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((Znth c piles 0) = 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH7 : (0 <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (IntArray.full a_pre n_pre piles )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
|--
  “ ((c + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : (0 <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : (0 <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : (0 <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c <> n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : (0 <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ ((c <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_8 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c <> n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : (0 <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c <> n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : (0 <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre piles )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles 0)) /\ ((Znth i_3 piles 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))),
  (IntArray.full a_pre n_pre piles )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (piles))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < 0)) -> ((Znth i_2 piles 0) = 1)) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles 0)) /\ ((Znth i_3 piles 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))),
  TT && emp 
|--
  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < 0)) -> ((Znth i_2 piles 0) = 1)) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (piles: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles 0)) /\ ((Znth i_3 piles 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))),
  forall (i_2: Z), (((0 <= i_2) /\ (i_2 < 0)) -> ((Znth i_2 piles 0) = 1))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (piles: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles 0)) /\ ((Znth i_3 piles 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))),
  forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))
.

Definition solver_entail_wit_2 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((Znth c piles 0) = 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH7 : (0 <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (IntArray.full a_pre n_pre piles )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (piles))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000))) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= n_pre) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (c + 1 ))) -> ((Znth i_2 piles 0) = 1)) ”
  &&  (IntArray.full a_pre n_pre piles )
.

Definition solver_entail_wit_3_1 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (IntArray.full a_pre n_pre piles )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (piles))) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= n_pre) ”
  &&  “ (LeadingOnes piles c ) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : (c >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  TT && emp 
|--
  “ (LeadingOnes piles c ) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 :=
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : (c >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (LeadingOnes piles c )
.

Definition solver_entail_wit_3_2 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((Znth c piles 0) <> 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH7 : (0 <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (IntArray.full a_pre n_pre piles )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (piles))) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= n_pre) ”
  &&  “ (LeadingOnes piles c ) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : ((Znth c piles 0) <> 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH7 : (0 <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  TT && emp 
|--
  “ (LeadingOnes piles c ) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 :=
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : ((Znth c piles 0) <> 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH7 : (0 <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (LeadingOnes piles c )
.

Definition solver_return_wit_1 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((c % ( 2 ) ) <> 0)) (PreH2 : (c <> n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  (IntArray.full a_pre n_pre piles )
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : ((c % ( 2 ) ) <> 0)) (PreH2 : (c <> n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  TT && emp 
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  emp
).

Definition solver_return_wit_2 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((c % ( 2 ) ) = 0)) (PreH2 : (c <> n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  (IntArray.full a_pre n_pre piles )
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : ((c % ( 2 ) ) = 0)) (PreH2 : (c <> n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  TT && emp 
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  emp
).

Definition solver_return_wit_3 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((n_pre % ( 2 ) ) <> 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  (IntArray.full a_pre n_pre piles )
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : ((n_pre % ( 2 ) ) <> 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  TT && emp 
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  emp
).

Definition solver_return_wit_4 :=
(
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : ((n_pre % ( 2 ) ) = 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  (IntArray.full a_pre n_pre piles )
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  (IntArray.full a_pre n_pre piles )
) \/
(
forall (piles: (@list Z)) (n_pre: Z) (c: Z) (PreH1 : ((n_pre % ( 2 ) ) = 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c )),
  TT && emp 
|--
  EX (out: Z),
  “ (Spec piles out ) ”
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 :=
forall (piles: (@list Z)) (a_pre: Z) (n_pre: Z) (c: Z) (PreH1 : (c < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000)))) (PreH6 : (0 <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1))),
  (IntArray.full a_pre n_pre piles )
|--
  “ (c < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (piles))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i piles 0)) /\ ((Znth i piles 0) <= 1000000000))) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= n_pre) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < c)) -> ((Znth i_2 piles 0) = 1)) ”
  &&  (((a_pre + (c * sizeof(INT)))) # Int  |-> (Znth c piles 0))
  **  (IntArray.missing_i a_pre c 0 n_pre piles )
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
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
