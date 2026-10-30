From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (2 <= ((Zlength (years)) + 1 ))) (PreH2 : (((Zlength (years)) + 1 ) <= 100)) (PreH3 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1 ))),
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i (cons (0) (years)) 0) ))
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 :=
(
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ ((ans + (Znth i (cons (0) (years)) 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (ans + (Znth i (cons (0) (years)) 0) )) ”
) \/
(
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ ((ans + (Znth i (cons (0) (years)) 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (ans + (Znth i (cons (0) (years)) 0) )) ”
).

Definition solver_safety_wit_3_split_goal_1 :=
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ ((ans + (Znth i (cons (0) (years)) 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_3_split_goal_2 :=
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ ((INT_MIN) <= (ans + (Znth i (cons (0) (years)) 0) )) ”
.

Definition solver_entail_wit_1 :=
(
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (2 <= ((Zlength (years)) + 1 ))) (PreH2 : (((Zlength (years)) + 1 ) <= 100)) (PreH3 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years 0)) /\ ((Znth idx_2 years 0) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1 ))),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ (2 <= ((Zlength (years)) + 1 )) ”
  &&  “ (((Zlength (years)) + 1 ) <= 100) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100))) ”
  &&  “ (1 <= a_pre) ”
  &&  “ (a_pre <= a_pre) ”
  &&  “ (a_pre <= b_pre) ”
  &&  “ (b_pre <= ((Zlength (years)) + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (100 * (a_pre - a_pre ) )) ”
  &&  “ (Spec ((Zlength (years)) + 1 ) years a_pre a_pre 0 ) ”
  &&  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
) \/
(
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (PreH1 : (2 <= ((Zlength (years)) + 1 ))) (PreH2 : (((Zlength (years)) + 1 ) <= 100)) (PreH3 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years 0)) /\ ((Znth idx_2 years 0) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1 ))),
  TT && emp 
|--
  “ (Spec ((Zlength (years)) + 1 ) years a_pre a_pre 0 ) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (PreH1 : (2 <= ((Zlength (years)) + 1 ))) (PreH2 : (((Zlength (years)) + 1 ) <= 100)) (PreH3 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years 0)) /\ ((Znth idx_2 years 0) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1 ))),
  (Spec ((Zlength (years)) + 1 ) years a_pre a_pre 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (PreH1 : (2 <= ((Zlength (years)) + 1 ))) (PreH2 : (((Zlength (years)) + 1 ) <= 100)) (PreH3 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years 0)) /\ ((Znth idx_2 years 0) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1 ))),
  forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))
.

Definition solver_entail_wit_2 :=
(
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ (2 <= ((Zlength (years)) + 1 )) ”
  &&  “ (((Zlength (years)) + 1 ) <= 100) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100))) ”
  &&  “ (1 <= a_pre) ”
  &&  “ (a_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= b_pre) ”
  &&  “ (b_pre <= ((Zlength (years)) + 1 )) ”
  &&  “ (0 <= (ans + (Znth i (cons (0) (years)) 0) )) ”
  &&  “ ((ans + (Znth i (cons (0) (years)) 0) ) <= (100 * ((i + 1 ) - a_pre ) )) ”
  &&  “ (Spec ((Zlength (years)) + 1 ) years a_pre (i + 1 ) (ans + (Znth i (cons (0) (years)) 0) ) ) ”
  &&  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
) \/
(
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  TT && emp 
|--
  “ (Spec ((Zlength (years)) + 1 ) years a_pre (i + 1 ) (ans + (Znth i (cons (0) (years)) 0) ) ) ”
  &&  “ ((ans + (Znth i (cons (0) (years)) 0) ) <= (100 * ((i + 1 ) - a_pre ) )) ”
  &&  “ (0 <= (ans + (Znth i (cons (0) (years)) 0) )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (Spec ((Zlength (years)) + 1 ) years a_pre (i + 1 ) (ans + (Znth i (cons (0) (years)) 0) ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  ((ans + (Znth i (cons (0) (years)) 0) ) <= (100 * ((i + 1 ) - a_pre ) ))
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (0 <= (ans + (Znth i (cons (0) (years)) 0) ))
.

Definition solver_return_wit_1 :=
(
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i >= b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ (Spec ((Zlength (years)) + 1 ) years a_pre b_pre ans ) ”
  &&  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
) \/
(
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i >= b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  TT && emp 
|--
  “ (Spec ((Zlength (years)) + 1 ) years a_pre b_pre ans ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (years: (@list Z)) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i >= b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (Spec ((Zlength (years)) + 1 ) years a_pre b_pre ans )
.

Definition solver_partial_solve_wit_1 :=
forall (years: (@list Z)) (d_pre: Z) (a_pre: Z) (b_pre: Z) (ans: Z) (i: Z) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1 ))) (PreH3 : (((Zlength (years)) + 1 ) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1 ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= (100 * (i - a_pre ) ))) (PreH11 : (Spec ((Zlength (years)) + 1 ) years a_pre i ans )),
  (IntArray.full d_pre ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
|--
  “ (i < b_pre) ”
  &&  “ (2 <= ((Zlength (years)) + 1 )) ”
  &&  “ (((Zlength (years)) + 1 ) <= 100) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years 0)) /\ ((Znth idx years 0) <= 100))) ”
  &&  “ (1 <= a_pre) ”
  &&  “ (a_pre <= i) ”
  &&  “ (i <= b_pre) ”
  &&  “ (b_pre <= ((Zlength (years)) + 1 )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= (100 * (i - a_pre ) )) ”
  &&  “ (Spec ((Zlength (years)) + 1 ) years a_pre i ans ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (cons (0) (years)) 0))
  **  (IntArray.missing_i d_pre i 0 ((Zlength (years)) + 1 ) (cons (0) (years)) )
  **  (IntArray.undef_seg d_pre ((Zlength (years)) + 1 ) 101 )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
