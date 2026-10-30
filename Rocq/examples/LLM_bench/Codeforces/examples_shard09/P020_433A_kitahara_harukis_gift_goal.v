From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth i weights 0) = 100) \/ ((Znth i weights 0) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))),
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth i weights 0) = 100) \/ ((Znth i weights 0) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> (total + ((Znth i weights 0) ÷ 100 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
|--
  “ ((total + ((Znth i weights 0) ÷ 100 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (total + ((Znth i weights 0) ÷ 100 ) )) ”
) \/
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
|--
  “ ((total + ((Znth i weights 0) ÷ 100 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (total + ((Znth i weights 0) ÷ 100 ) )) ”
).

Definition solver_safety_wit_4_split_goal_1 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
|--
  “ ((total + ((Znth i weights 0) ÷ 100 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
|--
  “ ((INT_MIN) <= (total + ((Znth i weights 0) ÷ 100 ) )) ”
.

Definition solver_safety_wit_5 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
|--
  “ (((Znth i weights 0) <> (INT_MIN)) \/ (100 <> (-1))) ”
  &&  “ (100 <> 0) ”
.

Definition solver_safety_wit_6 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
|--
  “ (100 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 100) ”
.

Definition solver_safety_wit_7 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ ((total <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_8 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : (PrefixUnitTotal weights n_pre total )) (PreH8 : (Spec weights 0 )) (PreH9 : (SolverReturnBridge 0 0 )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= (205 * sizeof(CHAR)))) (PreH10 : ((205 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= (205 * sizeof(CHAR)))) (PreH10 : ((205 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 (repeat_Z (0) (205)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 (repeat_Z (0) (205)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (ReachTable weights 0 total reach_l )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "u" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ (((Znth i weights 0) <> (INT_MIN)) \/ (100 <> (-1))) ”
  &&  “ (100 <> 0) ”
.

Definition solver_safety_wit_16 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l )),
  (IntArray.full w_pre n_pre weights )
  **  ((( &( "u" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ (100 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 100) ”
.

Definition solver_safety_wit_17 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ ((s - u ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (s - u )) ”
.

Definition solver_safety_wit_18 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l )) (PreH18 : ((Znth (s - u ) reach_l 0) <> 0)),
  (CharArray.full ( &( "reach" ) ) 205 reach_l )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l )) (PreH18 : ((Znth (s - u ) reach_l 0) <> 0)),
  (CharArray.full ( &( "reach" ) ) 205 (replace_Znth (s) (1) (reach_l)) )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ ((s - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (s - 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l )) (PreH18 : ((Znth (s - u ) reach_l 0) = 0)),
  (CharArray.full ( &( "reach" ) ) 205 reach_l )
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full w_pre n_pre weights )
|--
  “ ((s - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (s - 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (i: Z) (u: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1 ) total reach_l )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (0 <= (total ÷ 2 ))) (PreH9 : ((total ÷ 2 ) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total )) (PreH11 : (ReachTable weights n_pre total reach_l )) (PreH12 : (Spec weights (Znth (total ÷ 2 ) reach_l 0) )) (PreH13 : (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ ((total <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_23 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (0 <= (total ÷ 2 ))) (PreH9 : ((total ÷ 2 ) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total )) (PreH11 : (ReachTable weights n_pre total reach_l )) (PreH12 : (Spec weights (Znth (total ÷ 2 ) reach_l 0) )) (PreH13 : (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) )),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_entail_wit_1 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth i weights 0) = 100) \/ ((Znth i weights 0) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))),
  (IntArray.full w_pre n_pre weights )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (2 * 0 )) ”
  &&  “ (PrefixUnitTotal weights 0 0 ) ”
  &&  (IntArray.full w_pre n_pre weights )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth i weights 0) = 100) \/ ((Znth i weights 0) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))),
  TT && emp 
|--
  “ (PrefixUnitTotal weights 0 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth i weights 0) = 100) \/ ((Znth i weights 0) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))),
  (PrefixUnitTotal weights 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth i weights 0) = 100) \/ ((Znth i weights 0) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_2 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (total + ((Znth i weights 0) ÷ 100 ) )) ”
  &&  “ ((total + ((Znth i weights 0) ÷ 100 ) ) <= (2 * (i + 1 ) )) ”
  &&  “ (PrefixUnitTotal weights (i + 1 ) (total + ((Znth i weights 0) ÷ 100 ) ) ) ”
  &&  (IntArray.full w_pre n_pre weights )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  TT && emp 
|--
  “ (PrefixUnitTotal weights (i + 1 ) (total + ((Znth i weights 0) ÷ 100 ) ) ) ”
  &&  “ ((total + ((Znth i weights 0) ÷ 100 ) ) <= (2 * (i + 1 ) )) ”
  &&  “ (0 <= (total + ((Znth i weights 0) ÷ 100 ) )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (PrefixUnitTotal weights (i + 1 ) (total + ((Znth i weights 0) ÷ 100 ) ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  ((total + ((Znth i weights 0) ÷ 100 ) ) <= (2 * (i + 1 ) ))
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (0 <= (total + ((Znth i weights 0) ÷ 100 ) ))
.

Definition solver_entail_wit_3 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) <> 0)),
  (IntArray.full w_pre n_pre weights )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (Spec weights 0 ) ”
  &&  “ (SolverReturnBridge 0 0 ) ”
  &&  (IntArray.full w_pre n_pre weights )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) <> 0)),
  TT && emp 
|--
  “ (SolverReturnBridge 0 0 ) ”
  &&  “ (Spec weights 0 ) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) <> 0)),
  (SolverReturnBridge 0 0 )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) <> 0)),
  (Spec weights 0 )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) <> 0)),
  (PrefixUnitTotal weights n_pre total )
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) <> 0)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_4 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) = 0)),
  (CharArray.undef_full ( &( "reach" ) ) 205 )
  **  (IntArray.full w_pre n_pre weights )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= (205 * sizeof(CHAR))) ”
  &&  “ ((205 * sizeof(CHAR)) < INT_MAX) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) = 0)),
  (CharArray.undef_full ( &( "reach" ) ) 205 )
|--
  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) = 0)),
  (CharArray.undef_full ( &( "reach" ) ) 205 )
|--
  “ (PrefixUnitTotal weights n_pre total ) ”
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) = 0)),
  (CharArray.undef_full ( &( "reach" ) ) 205 )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
.

Definition solver_entail_wit_4_split_goal_spatial :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )) (PreH11 : ((total % ( 2 ) ) = 0)),
  (CharArray.undef_full ( &( "reach" ) ) 205 )
|--
  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
.

Definition solver_entail_wit_5 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (retval: Z) (PreH1 : (retval = (( &( "reach" ) ) + (0 * sizeof(CHAR))))) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= (205 * sizeof(CHAR)))) (PreH11 : ((205 * sizeof(CHAR)) < INT_MAX)),
  (CharArray.full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) (repeat_Z (0) ((205 * sizeof(CHAR)))) )
  **  (IntArray.full w_pre n_pre weights )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 (repeat_Z (0) (205)) )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (retval: Z) (PreH1 : (retval = (( &( "reach" ) ) + (0 * sizeof(CHAR))))) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= (205 * sizeof(CHAR)))) (PreH11 : ((205 * sizeof(CHAR)) < INT_MAX)),
  (CharArray.full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) (repeat_Z (0) ((205 * sizeof(CHAR)))) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  (CharArray.full ( &( "reach" ) ) 205 (repeat_Z (0) (205)) )
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (retval: Z) (PreH1 : (retval = (( &( "reach" ) ) + (0 * sizeof(CHAR))))) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= (205 * sizeof(CHAR)))) (PreH11 : ((205 * sizeof(CHAR)) < INT_MAX)),
  (CharArray.full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) (repeat_Z (0) ((205 * sizeof(CHAR)))) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
.

Definition solver_entail_wit_5_split_goal_spatial :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (retval: Z) (PreH1 : (retval = (( &( "reach" ) ) + (0 * sizeof(CHAR))))) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= (205 * sizeof(CHAR)))) (PreH11 : ((205 * sizeof(CHAR)) < INT_MAX)),
  (CharArray.full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) (repeat_Z (0) ((205 * sizeof(CHAR)))) )
|--
  (CharArray.full ( &( "reach" ) ) 205 (repeat_Z (0) (205)) )
.

Definition solver_entail_wit_6 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  (CharArray.full ( &( "reach" ) ) 205 (replace_Znth (0) (1) ((repeat_Z (0) (205)))) )
  **  (IntArray.full w_pre n_pre weights )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (ReachTable weights 0 total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  TT && emp 
|--
  “ (ReachTable weights 0 total (replace_Znth (0) (1) ((repeat_Z (0) (205)))) ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  (ReachTable weights 0 total (replace_Znth (0) (1) ((repeat_Z (0) (205)))) )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_7 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (ReachTable weights 0 total reach_l_2 )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l_2 )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (ReachTable weights 0 total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (ReachTable weights 0 total reach_l_2 )),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (total: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (ReachTable weights 0 total reach_l_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_8 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l_2 )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (((Znth i weights 0) ÷ 100 ) = ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (1 <= ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (((Znth i weights 0) ÷ 100 ) <= 2) ”
  &&  “ ((((Znth i weights 0) ÷ 100 ) - 1 ) <= total) ”
  &&  “ (total <= total) ”
  &&  “ (ReachInnerProgress weights i total total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  TT && emp 
|--
  “ (ReachInnerProgress weights i total total reach_l_2 ) ”
  &&  “ ((((Znth i weights 0) ÷ 100 ) - 1 ) <= total) ”
  &&  “ (((Znth i weights 0) ÷ 100 ) <= 2) ”
  &&  “ (1 <= ((Znth i weights 0) ÷ 100 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (ReachInnerProgress weights i total total reach_l_2 )
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  ((((Znth i weights 0) ÷ 100 ) - 1 ) <= total)
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (((Znth i weights 0) ÷ 100 ) <= 2)
.

Definition solver_entail_wit_8_split_goal_4 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (1 <= ((Znth i weights 0) ÷ 100 ))
.

Definition solver_entail_wit_8_split_goal_5 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_9 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s < u)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l_2 )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (u = ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= 2) ”
  &&  “ (ReachTable weights (i + 1 ) total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s < u)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )),
  TT && emp 
|--
  “ (ReachTable weights (i + 1 ) total reach_l_2 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s < u)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )),
  (ReachTable weights (i + 1 ) total reach_l_2 )
.

Definition solver_entail_wit_9_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s < u)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_10_1 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )) (PreH18 : ((Znth (s - u ) reach_l_2 0) <> 0)),
  (CharArray.full ( &( "reach" ) ) 205 (replace_Znth (s) (1) (reach_l_2)) )
  **  (IntArray.full w_pre n_pre weights )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (u = ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= 2) ”
  &&  “ ((u - 1 ) <= (s - 1 )) ”
  &&  “ ((s - 1 ) <= total) ”
  &&  “ (ReachInnerProgress weights i (s - 1 ) total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )) (PreH18 : ((Znth (s - u ) reach_l_2 0) <> 0)),
  TT && emp 
|--
  “ (ReachInnerProgress weights i (s - 1 ) total (replace_Znth (s) (1) (reach_l_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )) (PreH18 : ((Znth (s - u ) reach_l_2 0) <> 0)),
  (ReachInnerProgress weights i (s - 1 ) total (replace_Znth (s) (1) (reach_l_2)) )
.

Definition solver_entail_wit_10_2 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )) (PreH18 : ((Znth (s - u ) reach_l_2 0) = 0)),
  (CharArray.full ( &( "reach" ) ) 205 reach_l_2 )
  **  (IntArray.full w_pre n_pre weights )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (u = ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= 2) ”
  &&  “ ((u - 1 ) <= (s - 1 )) ”
  &&  “ ((s - 1 ) <= total) ”
  &&  “ (ReachInnerProgress weights i (s - 1 ) total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )) (PreH18 : ((Znth (s - u ) reach_l_2 0) = 0)),
  TT && emp 
|--
  “ (ReachInnerProgress weights i (s - 1 ) total reach_l_2 ) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2 )) (PreH18 : ((Znth (s - u ) reach_l_2 0) = 0)),
  (ReachInnerProgress weights i (s - 1 ) total reach_l_2 )
.

Definition solver_entail_wit_11 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (total: Z) (i: Z) (u: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1 ) total reach_l_2 )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l_2 )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (ReachTable weights (i + 1 ) total reach_l ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (total: Z) (i: Z) (u: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1 ) total reach_l_2 )),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (total: Z) (i: Z) (u: Z) (PreH1 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1 ) total reach_l_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_entail_wit_12 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l_2 )
|--
  EX (reach_l: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (0 <= (total ÷ 2 )) ”
  &&  “ ((total ÷ 2 ) < 205) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (ReachTable weights n_pre total reach_l ) ”
  &&  “ (Spec weights (Znth (total ÷ 2 ) reach_l 0) ) ”
  &&  “ (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) ) ”
  &&  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  TT && emp 
|--
  “ (SolverReturnBridge (Znth (total ÷ 2 ) reach_l_2 0) (Znth (total ÷ 2 ) reach_l_2 0) ) ”
  &&  “ (Spec weights (Znth (total ÷ 2 ) reach_l_2 0) ) ”
  &&  “ (ReachTable weights n_pre total reach_l_2 ) ”
  &&  “ ((total ÷ 2 ) < 205) ”
  &&  “ (0 <= (total ÷ 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (SolverReturnBridge (Znth (total ÷ 2 ) reach_l_2 0) (Znth (total ÷ 2 ) reach_l_2 0) )
.

Definition solver_entail_wit_12_split_goal_2 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (Spec weights (Znth (total ÷ 2 ) reach_l_2 0) )
.

Definition solver_entail_wit_12_split_goal_3 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (ReachTable weights n_pre total reach_l_2 )
.

Definition solver_entail_wit_12_split_goal_4 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  ((total ÷ 2 ) < 205)
.

Definition solver_entail_wit_12_split_goal_5 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  (0 <= (total ÷ 2 ))
.

Definition solver_entail_wit_12_split_goal_6 :=
forall (weights: (@list Z)) (n_pre: Z) (reach_l_2: (@list Z)) (i: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 weights 0) = 100) \/ ((Znth j_2 weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))
.

Definition solver_return_wit_1 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (0 <= (total ÷ 2 ))) (PreH9 : ((total ÷ 2 ) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total )) (PreH11 : (ReachTable weights n_pre total reach_l )) (PreH12 : (Spec weights (Znth (total ÷ 2 ) reach_l 0) )) (PreH13 : (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) )),
  (IntArray.full w_pre n_pre weights )
|--
  EX (out: Z),
  “ (Spec weights out ) ”
  &&  “ (SolverReturnBridge out (Znth (total ÷ 2 ) reach_l 0) ) ”
  &&  (IntArray.full w_pre n_pre weights )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (0 <= (total ÷ 2 ))) (PreH9 : ((total ÷ 2 ) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total )) (PreH11 : (ReachTable weights n_pre total reach_l )) (PreH12 : (Spec weights (Znth (total ÷ 2 ) reach_l 0) )) (PreH13 : (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) )),
  TT && emp 
|--
  EX (out: Z),
  “ (Spec weights out ) ”
  &&  “ (SolverReturnBridge out (Znth (total ÷ 2 ) reach_l 0) ) ”
  &&  emp
).

Definition solver_return_wit_2 :=
(
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : (PrefixUnitTotal weights n_pre total )) (PreH8 : (Spec weights 0 )) (PreH9 : (SolverReturnBridge 0 0 )),
  (IntArray.full w_pre n_pre weights )
|--
  EX (out: Z),
  “ (Spec weights out ) ”
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  (IntArray.full w_pre n_pre weights )
) \/
(
forall (weights: (@list Z)) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : (PrefixUnitTotal weights n_pre total )) (PreH8 : (Spec weights 0 )) (PreH9 : (SolverReturnBridge 0 0 )),
  TT && emp 
|--
  EX (out: Z),
  “ (Spec weights out ) ”
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (2 * i ))) (PreH10 : (PrefixUnitTotal weights i total )),
  (IntArray.full w_pre n_pre weights )
|--
  “ (i < n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (2 * i )) ”
  &&  “ (PrefixUnitTotal weights i total ) ”
  &&  (((w_pre + (i * sizeof(INT)))) # Int  |-> (Znth i weights 0))
  **  (IntArray.missing_i w_pre i 0 n_pre weights )
.

Definition solver_partial_solve_wit_2_pure :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= (205 * sizeof(CHAR)))) (PreH10 : ((205 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full w_pre n_pre weights )
  **  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
|--
  “ (0 <= (205 * sizeof(CHAR))) ”
  &&  “ ((205 * sizeof(CHAR)) < INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 127) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )) (PreH9 : (0 <= (205 * sizeof(CHAR)))) (PreH10 : ((205 * sizeof(CHAR)) < INT_MAX)),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
|--
  “ (0 <= (205 * sizeof(CHAR))) ”
  &&  “ ((205 * sizeof(CHAR)) < INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 127) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= (205 * sizeof(CHAR))) ”
  &&  “ ((205 * sizeof(CHAR)) < INT_MAX) ”
  &&  (CharArray.undef_full (( &( "reach" ) ) + (0 * sizeof(CHAR))) (205 * sizeof(CHAR)) )
  **  (IntArray.full w_pre n_pre weights )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (PrefixUnitTotal weights n_pre total )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 (repeat_Z (0) (205)) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  (((( &( "reach" ) ) + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i ( &( "reach" ) ) 0 0 205 (repeat_Z (0) (205)) )
  **  (IntArray.full w_pre n_pre weights )
.

Definition solver_partial_solve_wit_4 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (i: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ (i < n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (ReachTable weights i total reach_l ) ”
  &&  (((w_pre + (i * sizeof(INT)))) # Int  |-> (Znth i weights 0))
  **  (IntArray.missing_i w_pre i 0 n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
.

Definition solver_partial_solve_wit_5 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ (s >= u) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (u = ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= 2) ”
  &&  “ ((u - 1 ) <= s) ”
  &&  “ (s <= total) ”
  &&  “ (ReachInnerProgress weights i s total reach_l ) ”
  &&  (((( &( "reach" ) ) + ((s - u ) * sizeof(CHAR)))) # Char  |-> (Znth (s - u ) reach_l 0))
  **  (CharArray.missing_i ( &( "reach" ) ) (s - u ) 0 205 reach_l )
  **  (IntArray.full w_pre n_pre weights )
.

Definition solver_partial_solve_wit_6 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (s: Z) (u: Z) (i: Z) (total: Z) (PreH1 : (s >= u)) (PreH2 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((total % ( 2 ) ) = 0)) (PreH9 : (PrefixUnitTotal weights n_pre total )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = ((Znth i weights 0) ÷ 100 ))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1 ) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l )) (PreH18 : ((Znth (s - u ) reach_l 0) <> 0)),
  (CharArray.full ( &( "reach" ) ) 205 reach_l )
  **  (IntArray.full w_pre n_pre weights )
|--
  “ (s >= u) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (u = ((Znth i weights 0) ÷ 100 )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= 2) ”
  &&  “ ((u - 1 ) <= s) ”
  &&  “ (s <= total) ”
  &&  “ (ReachInnerProgress weights i s total reach_l ) ”
  &&  “ ((Znth (s - u ) reach_l 0) <> 0) ”
  &&  (((( &( "reach" ) ) + (s * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i ( &( "reach" ) ) s 0 205 reach_l )
  **  (IntArray.full w_pre n_pre weights )
.

Definition solver_partial_solve_wit_7 :=
forall (weights: (@list Z)) (w_pre: Z) (n_pre: Z) (reach_l: (@list Z)) (total: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((total % ( 2 ) ) = 0)) (PreH8 : (0 <= (total ÷ 2 ))) (PreH9 : ((total ÷ 2 ) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total )) (PreH11 : (ReachTable weights n_pre total reach_l )) (PreH12 : (Spec weights (Znth (total ÷ 2 ) reach_l 0) )) (PreH13 : (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) )),
  (IntArray.full w_pre n_pre weights )
  **  (CharArray.full ( &( "reach" ) ) 205 reach_l )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j weights 0) = 100) \/ ((Znth j weights 0) = 200))) ”
  &&  “ (n_pre = (Zlength (weights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= 200) ”
  &&  “ ((total % ( 2 ) ) = 0) ”
  &&  “ (0 <= (total ÷ 2 )) ”
  &&  “ ((total ÷ 2 ) < 205) ”
  &&  “ (PrefixUnitTotal weights n_pre total ) ”
  &&  “ (ReachTable weights n_pre total reach_l ) ”
  &&  “ (Spec weights (Znth (total ÷ 2 ) reach_l 0) ) ”
  &&  “ (SolverReturnBridge (Znth (total ÷ 2 ) reach_l 0) (Znth (total ÷ 2 ) reach_l 0) ) ”
  &&  (((( &( "reach" ) ) + ((total ÷ 2 ) * sizeof(CHAR)))) # Char  |-> (Znth (total ÷ 2 ) reach_l 0))
  **  (CharArray.missing_i ( &( "reach" ) ) (total ÷ 2 ) 0 205 reach_l )
  **  (IntArray.full w_pre n_pre weights )
.

Module Type VC_Correct.

Include string_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
