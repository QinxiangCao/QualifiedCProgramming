From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P052_1168A_increasing_by_modulo_lib.
Local Open Scope sac.

(*----- Function feasible -----*)

Definition feasible_safety_wit_1 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (PreH1 : (1 <= mv)) (PreH2 : (mv <= 300000)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 300000)) (PreH5 : (0 <= x_pre)) (PreH6 : (x_pre < mv)) (PreH7 : ((Zlength (values)) = nv)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))),
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_2 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (PreH1 : (1 <= mv)) (PreH2 : (mv <= 300000)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 300000)) (PreH5 : (0 <= x_pre)) (PreH6 : (x_pre < mv)) (PreH7 : ((Zlength (values)) = nv)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "last" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_3 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (i < nv)) (PreH2 : (1 <= mv)) (PreH3 : (mv <= 300000)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 300000)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre < mv)) (PreH8 : ((Zlength (values)) = nv)) (PreH9 : (0 <= i)) (PreH10 : (i <= nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH12 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i values 0) + x_pre )) ”
.

Definition feasible_safety_wit_4 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) < mv)) (PreH2 : (i < nv)) (PreH3 : (1 <= mv)) (PreH4 : (mv <= 300000)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 300000)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre < mv)) (PreH9 : ((Zlength (values)) = nv)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv)) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH13 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i values 0) + x_pre )) ”
.

Definition feasible_safety_wit_5 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) < last)) (PreH2 : (((Znth i values 0) + x_pre ) < mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_6 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) >= mv)) (PreH2 : (i < nv)) (PreH3 : (1 <= mv)) (PreH4 : (mv <= 300000)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 300000)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre < mv)) (PreH9 : ((Zlength (values)) = nv)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv)) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH13 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "wrapped" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((((Znth i values 0) + x_pre ) <> (INT_MIN)) \/ (mv <> (-1))) ”
  &&  “ (mv <> 0) ”
.

Definition feasible_safety_wit_7 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) >= mv)) (PreH2 : (i < nv)) (PreH3 : (1 <= mv)) (PreH4 : (mv <= 300000)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 300000)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre < mv)) (PreH9 : ((Zlength (values)) = nv)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv)) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH13 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "wrapped" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i values 0) + x_pre )) ”
.

Definition feasible_safety_wit_8 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) > last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_9 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_10 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) < last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_11 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_12 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) >= last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_13 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (i >= nv)) (PreH2 : (1 <= mv)) (PreH3 : (mv <= 300000)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 300000)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre < mv)) (PreH8 : ((Zlength (values)) = nv)) (PreH9 : (0 <= i)) (PreH10 : (i <= nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH12 : (GreedyPrefixState mv values x_pre i last )),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_entail_wit_1 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (PreH1 : (1 <= mv)) (PreH2 : (mv <= 300000)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 300000)) (PreH5 : (0 <= x_pre)) (PreH6 : (x_pre < mv)) (PreH7 : ((Zlength (values)) = nv)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) < mv)))),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
|--
  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre 0 0 ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (PreH1 : (1 <= mv)) (PreH2 : (mv <= 300000)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 300000)) (PreH5 : (0 <= x_pre)) (PreH6 : (x_pre < mv)) (PreH7 : ((Zlength (values)) = nv)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) < mv)))),
  TT && emp 
|--
  “ (GreedyPrefixState mv values x_pre 0 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  emp
).

Definition feasible_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (PreH1 : (1 <= mv)) (PreH2 : (mv <= 300000)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 300000)) (PreH5 : (0 <= x_pre)) (PreH6 : (x_pre < mv)) (PreH7 : ((Zlength (values)) = nv)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) < mv)))),
  (GreedyPrefixState mv values x_pre 0 0 )
.

Definition feasible_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (PreH1 : (1 <= mv)) (PreH2 : (mv <= 300000)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 300000)) (PreH5 : (0 <= x_pre)) (PreH6 : (x_pre < mv)) (PreH7 : ((Zlength (values)) = nv)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) < mv)))),
  forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))
.

Definition feasible_entail_wit_2_1 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) > last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre (i + 1 ) (Znth i values 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) > last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ (GreedyPrefixState mv values x_pre (i + 1 ) (Znth i values 0) ) ”
  &&  emp
).

Definition feasible_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) > last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (GreedyPrefixState mv values x_pre (i + 1 ) (Znth i values 0) )
.

Definition feasible_entail_wit_2_2 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre (i + 1 ) last ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ (GreedyPrefixState mv values x_pre (i + 1 ) last ) ”
  &&  emp
).

Definition feasible_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (GreedyPrefixState mv values x_pre (i + 1 ) last )
.

Definition feasible_entail_wit_2_3 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) < last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre (i + 1 ) (Znth i values 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) < last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ (GreedyPrefixState mv values x_pre (i + 1 ) (Znth i values 0) ) ”
  &&  emp
).

Definition feasible_entail_wit_2_3_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) < last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (GreedyPrefixState mv values x_pre (i + 1 ) (Znth i values 0) )
.

Definition feasible_entail_wit_2_4 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre (i + 1 ) last ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ (GreedyPrefixState mv values x_pre (i + 1 ) last ) ”
  &&  emp
).

Definition feasible_entail_wit_2_4_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) <= last)) (PreH2 : (((Znth i values 0) + x_pre ) >= mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  (GreedyPrefixState mv values x_pre (i + 1 ) last )
.

Definition feasible_entail_wit_2_5 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) >= last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre (i + 1 ) last ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) >= last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ (GreedyPrefixState mv values x_pre (i + 1 ) last ) ”
  &&  emp
).

Definition feasible_entail_wit_2_5_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) >= last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (GreedyPrefixState mv values x_pre (i + 1 ) last )
.

Definition feasible_return_wit_1 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (i >= nv)) (PreH2 : (1 <= mv)) (PreH3 : (mv <= 300000)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 300000)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre < mv)) (PreH8 : ((Zlength (values)) = nv)) (PreH9 : (0 <= i)) (PreH10 : (i <= nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH12 : (GreedyPrefixState mv values x_pre i last )),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
|--
  “ (0 <= 1) ”
  &&  “ (1 <= 1) ”
  &&  “ ((1 <> 0) <-> (Feasible mv values x_pre )) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (i >= nv)) (PreH2 : (1 <= mv)) (PreH3 : (mv <= 300000)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 300000)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre < mv)) (PreH8 : ((Zlength (values)) = nv)) (PreH9 : (0 <= i)) (PreH10 : (i <= nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH12 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ ((1 <> 0) <-> (Feasible mv values x_pre )) ”
  &&  emp
).

Definition feasible_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (i >= nv)) (PreH2 : (1 <= mv)) (PreH3 : (mv <= 300000)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 300000)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre < mv)) (PreH8 : ((Zlength (values)) = nv)) (PreH9 : (0 <= i)) (PreH10 : (i <= nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH12 : (GreedyPrefixState mv values x_pre i last )),
  ((1 <> 0) <-> (Feasible mv values x_pre ))
.

Definition feasible_return_wit_2 :=
(
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) < last)) (PreH2 : (((Znth i values 0) + x_pre ) < mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ ((0 <> 0) <-> (Feasible mv values x_pre )) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
) \/
(
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) < last)) (PreH2 : (((Znth i values 0) + x_pre ) < mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  TT && emp 
|--
  “ ((0 <> 0) <-> (Feasible mv values x_pre )) ”
  &&  emp
).

Definition feasible_return_wit_2_split_goal_1 :=
forall (values: (@list Z)) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) < last)) (PreH2 : (((Znth i values 0) + x_pre ) < mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  ((0 <> 0) <-> (Feasible mv values x_pre ))
.

Definition feasible_partial_solve_wit_1 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (i < nv)) (PreH2 : (1 <= mv)) (PreH3 : (mv <= 300000)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 300000)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre < mv)) (PreH8 : ((Zlength (values)) = nv)) (PreH9 : (0 <= i)) (PreH10 : (i <= nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH12 : (GreedyPrefixState mv values x_pre i last )),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr nv values )
|--
  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

Definition feasible_partial_solve_wit_2 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) < mv)) (PreH2 : (i < nv)) (PreH3 : (1 <= mv)) (PreH4 : (mv <= 300000)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 300000)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre < mv)) (PreH9 : ((Zlength (values)) = nv)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv)) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH13 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) < mv) ”
  &&  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

Definition feasible_partial_solve_wit_3 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) >= last)) (PreH2 : (((Znth i values 0) + x_pre ) < mv)) (PreH3 : (i < nv)) (PreH4 : (1 <= mv)) (PreH5 : (mv <= 300000)) (PreH6 : (1 <= nv)) (PreH7 : (nv <= 300000)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre < mv)) (PreH10 : ((Zlength (values)) = nv)) (PreH11 : (0 <= i)) (PreH12 : (i <= nv)) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH14 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) >= last) ”
  &&  “ (((Znth i values 0) + x_pre ) < mv) ”
  &&  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

Definition feasible_partial_solve_wit_4 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((Znth i values 0) > last)) (PreH2 : (((Znth i values 0) + x_pre ) >= last)) (PreH3 : (((Znth i values 0) + x_pre ) < mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((Znth i values 0) > last) ”
  &&  “ (((Znth i values 0) + x_pre ) >= last) ”
  &&  “ (((Znth i values 0) + x_pre ) < mv) ”
  &&  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

Definition feasible_partial_solve_wit_5 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) >= mv)) (PreH2 : (i < nv)) (PreH3 : (1 <= mv)) (PreH4 : (mv <= 300000)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 300000)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre < mv)) (PreH9 : ((Zlength (values)) = nv)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv)) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH13 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) >= mv) ”
  &&  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

Definition feasible_partial_solve_wit_6 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : (((Znth i values 0) + x_pre ) >= mv)) (PreH2 : (i < nv)) (PreH3 : (1 <= mv)) (PreH4 : (mv <= 300000)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 300000)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre < mv)) (PreH9 : ((Zlength (values)) = nv)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv)) (PreH12 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH13 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ (((Znth i values 0) + x_pre ) >= mv) ”
  &&  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

Definition feasible_partial_solve_wit_7 :=
forall (values: (@list Z)) (arr: Z) (mv: Z) (nv: Z) (x_pre: Z) (last: Z) (i: Z) (PreH1 : ((((Znth i values 0) + x_pre ) % ( mv ) ) < last)) (PreH2 : ((Znth i values 0) > last)) (PreH3 : (((Znth i values 0) + x_pre ) >= mv)) (PreH4 : (i < nv)) (PreH5 : (1 <= mv)) (PreH6 : (mv <= 300000)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 300000)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre < mv)) (PreH11 : ((Zlength (values)) = nv)) (PreH12 : (0 <= i)) (PreH13 : (i <= nv)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv)))) (PreH15 : (GreedyPrefixState mv values x_pre i last )),
  (IntArray.full arr nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
|--
  “ ((((Znth i values 0) + x_pre ) % ( mv ) ) < last) ”
  &&  “ ((Znth i values 0) > last) ”
  &&  “ (((Znth i values 0) + x_pre ) >= mv) ”
  &&  “ (i < nv) ”
  &&  “ (1 <= mv) ”
  &&  “ (mv <= 300000) ”
  &&  “ (1 <= nv) ”
  &&  “ (nv <= 300000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre < mv) ”
  &&  “ ((Zlength (values)) = nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < mv))) ”
  &&  “ (GreedyPrefixState mv values x_pre i last ) ”
  &&  (((arr + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i arr i 0 nv values )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "m" ) )) # Int  |-> mv)
  **  ((( &( "a" ) )) # Ptr  |-> arr)
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 0)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ ((mm_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mm_pre - 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 0)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo <= hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (((lo + hi ) <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo <= hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ ((lo + hi ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (lo + hi )) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo <= hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_7 :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
|--
  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
|--
  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
|--
  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
|--
  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) + 1 )) ”
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) + 1 )) ”
).

Definition solver_safety_wit_9_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_9_split_goal_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo > hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (values)))) -> ((0 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (nn_pre = (Zlength (values))) ”
  &&  “ (mm_pre = modulus) ”
  &&  “ (1 <= modulus) ”
  &&  “ (modulus <= 300000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 300000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= modulus) ”
  &&  “ ((-1) <= (mm_pre - 1 )) ”
  &&  “ ((mm_pre - 1 ) < modulus) ”
  &&  “ (0 <= ((mm_pre - 1 ) + 1 )) ”
  &&  “ (0 <= (mm_pre - 1 )) ”
  &&  “ ((mm_pre - 1 ) < modulus) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus))) ”
  &&  “ (SearchState modulus values 0 (mm_pre - 1 ) (mm_pre - 1 ) ) ”
  &&  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (values)))) -> ((0 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  TT && emp 
|--
  “ (SearchState modulus values 0 (modulus - 1 ) (modulus - 1 ) ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (values)))) -> ((0 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  (SearchState modulus values 0 (modulus - 1 ) (modulus - 1 ) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (PreH1 : (1 <= modulus)) (PreH2 : (modulus <= 300000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 300000)) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (values)))) -> ((0 <= (Znth i_2 values 0)) /\ ((Znth i_2 values 0) < modulus)))) (PreH6 : (nn_pre = (Zlength (values)))) (PreH7 : (mm_pre = modulus)),
  forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))
.

Definition solver_entail_wit_2_1 :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
|--
  “ (nn_pre = (Zlength (values))) ”
  &&  “ (mm_pre = modulus) ”
  &&  “ (1 <= modulus) ”
  &&  “ (modulus <= 300000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 300000) ”
  &&  “ (0 <= lo) ”
  &&  “ (lo <= modulus) ”
  &&  “ ((-1) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) - 1 ) < modulus) ”
  &&  “ (lo <= ((((lo + hi ) ÷ 2 ) - 1 ) + 1 )) ”
  &&  “ (0 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (((lo + hi ) ÷ 2 ) < modulus) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus))) ”
  &&  “ (SearchState modulus values lo (((lo + hi ) ÷ 2 ) - 1 ) ((lo + hi ) ÷ 2 ) ) ”
  &&  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  TT && emp 
|--
  “ (SearchState modulus values lo (((lo + hi ) ÷ 2 ) - 1 ) ((lo + hi ) ÷ 2 ) ) ”
  &&  “ (((lo + hi ) ÷ 2 ) < modulus) ”
  &&  “ (0 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (lo <= ((((lo + hi ) ÷ 2 ) - 1 ) + 1 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) - 1 ) < modulus) ”
  &&  “ ((-1) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  (SearchState modulus values lo (((lo + hi ) ÷ 2 ) - 1 ) ((lo + hi ) ÷ 2 ) )
.

Definition solver_entail_wit_2_1_split_goal_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  (((lo + hi ) ÷ 2 ) < modulus)
.

Definition solver_entail_wit_2_1_split_goal_3 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  (0 <= ((lo + hi ) ÷ 2 ))
.

Definition solver_entail_wit_2_1_split_goal_4 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  (lo <= ((((lo + hi ) ÷ 2 ) - 1 ) + 1 ))
.

Definition solver_entail_wit_2_1_split_goal_5 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((((lo + hi ) ÷ 2 ) - 1 ) < modulus)
.

Definition solver_entail_wit_2_1_split_goal_6 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval <> 0)),
  ((-1) <= (((lo + hi ) ÷ 2 ) - 1 ))
.

Definition solver_entail_wit_2_2 :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
|--
  “ (nn_pre = (Zlength (values))) ”
  &&  “ (mm_pre = modulus) ”
  &&  “ (1 <= modulus) ”
  &&  “ (modulus <= 300000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 300000) ”
  &&  “ (0 <= (((lo + hi ) ÷ 2 ) + 1 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= modulus) ”
  &&  “ ((-1) <= hi) ”
  &&  “ (hi < modulus) ”
  &&  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= (hi + 1 )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans < modulus) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus))) ”
  &&  “ (SearchState modulus values (((lo + hi ) ÷ 2 ) + 1 ) hi ans ) ”
  &&  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  TT && emp 
|--
  “ (SearchState modulus values (((lo + hi ) ÷ 2 ) + 1 ) hi ans ) ”
  &&  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= (hi + 1 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= modulus) ”
  &&  “ (0 <= (((lo + hi ) ÷ 2 ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  (SearchState modulus values (((lo + hi ) ÷ 2 ) + 1 ) hi ans )
.

Definition solver_entail_wit_2_2_split_goal_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((((lo + hi ) ÷ 2 ) + 1 ) <= (hi + 1 ))
.

Definition solver_entail_wit_2_2_split_goal_3 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  ((((lo + hi ) ÷ 2 ) + 1 ) <= modulus)
.

Definition solver_entail_wit_2_2_split_goal_4 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (Feasible modulus values ((lo + hi ) ÷ 2 ) ))) (PreH4 : (lo <= hi)) (PreH5 : (nn_pre = (Zlength (values)))) (PreH6 : (mm_pre = modulus)) (PreH7 : (1 <= modulus)) (PreH8 : (modulus <= 300000)) (PreH9 : (1 <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 300000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= modulus)) (PreH13 : ((-1) <= hi)) (PreH14 : (hi < modulus)) (PreH15 : (lo <= (hi + 1 ))) (PreH16 : (0 <= ans)) (PreH17 : (ans < modulus)) (PreH18 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH19 : (SearchState modulus values lo hi ans )) (PreH20 : (retval = 0)),
  (0 <= (((lo + hi ) ÷ 2 ) + 1 ))
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo > hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> 0)
|--
  “ (Spec modulus values ans ) ”
  &&  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> 0)
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo > hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  TT && emp 
|--
  “ (Spec modulus values ans ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo > hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  (Spec modulus values ans )
.

Definition solver_partial_solve_wit_1_pure :=
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo <= hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= modulus) ”
  &&  “ (modulus <= 300000) ”
  &&  “ (1 <= nn_pre) ”
  &&  “ (nn_pre <= 300000) ”
  &&  “ ((Zlength (values)) = nn_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nn_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < modulus))) ”
  &&  “ (((lo + hi ) ÷ 2 ) < modulus) ”
  &&  “ (0 <= ((lo + hi ) ÷ 2 )) ”
) \/
(
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (mm_pre <= INT_MAX)) (PreH5 : (nn_pre <= INT_MAX)) (PreH6 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (mm_pre >= INT_MIN)) (PreH11 : (nn_pre >= INT_MIN)) (PreH12 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH13 : (lo <= hi)) (PreH14 : (nn_pre = (Zlength (values)))) (PreH15 : (mm_pre = modulus)) (PreH16 : (1 <= modulus)) (PreH17 : (modulus <= 300000)) (PreH18 : (1 <= (Zlength (values)))) (PreH19 : ((Zlength (values)) <= 300000)) (PreH20 : (0 <= lo)) (PreH21 : (lo <= modulus)) (PreH22 : ((-1) <= hi)) (PreH23 : (hi < modulus)) (PreH24 : (lo <= (hi + 1 ))) (PreH25 : (0 <= ans)) (PreH26 : (ans < modulus)) (PreH27 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH28 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (0 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (((lo + hi ) ÷ 2 ) < modulus) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nn_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < modulus))) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (mm_pre <= INT_MAX)) (PreH5 : (nn_pre <= INT_MAX)) (PreH6 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (mm_pre >= INT_MIN)) (PreH11 : (nn_pre >= INT_MIN)) (PreH12 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH13 : (lo <= hi)) (PreH14 : (nn_pre = (Zlength (values)))) (PreH15 : (mm_pre = modulus)) (PreH16 : (1 <= modulus)) (PreH17 : (modulus <= 300000)) (PreH18 : (1 <= (Zlength (values)))) (PreH19 : ((Zlength (values)) <= 300000)) (PreH20 : (0 <= lo)) (PreH21 : (lo <= modulus)) (PreH22 : ((-1) <= hi)) (PreH23 : (hi < modulus)) (PreH24 : (lo <= (hi + 1 ))) (PreH25 : (0 <= ans)) (PreH26 : (ans < modulus)) (PreH27 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH28 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (0 <= ((lo + hi ) ÷ 2 )) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_2 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (mm_pre <= INT_MAX)) (PreH5 : (nn_pre <= INT_MAX)) (PreH6 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (mm_pre >= INT_MIN)) (PreH11 : (nn_pre >= INT_MIN)) (PreH12 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH13 : (lo <= hi)) (PreH14 : (nn_pre = (Zlength (values)))) (PreH15 : (mm_pre = modulus)) (PreH16 : (1 <= modulus)) (PreH17 : (modulus <= 300000)) (PreH18 : (1 <= (Zlength (values)))) (PreH19 : ((Zlength (values)) <= 300000)) (PreH20 : (0 <= lo)) (PreH21 : (lo <= modulus)) (PreH22 : ((-1) <= hi)) (PreH23 : (hi < modulus)) (PreH24 : (lo <= (hi + 1 ))) (PreH25 : (0 <= ans)) (PreH26 : (ans < modulus)) (PreH27 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH28 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (((lo + hi ) ÷ 2 ) < modulus) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_3 :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (mm_pre <= INT_MAX)) (PreH5 : (nn_pre <= INT_MAX)) (PreH6 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (mm_pre >= INT_MIN)) (PreH11 : (nn_pre >= INT_MIN)) (PreH12 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH13 : (lo <= hi)) (PreH14 : (nn_pre = (Zlength (values)))) (PreH15 : (mm_pre = modulus)) (PreH16 : (1 <= modulus)) (PreH17 : (modulus <= 300000)) (PreH18 : (1 <= (Zlength (values)))) (PreH19 : ((Zlength (values)) <= 300000)) (PreH20 : (0 <= lo)) (PreH21 : (lo <= modulus)) (PreH22 : ((-1) <= hi)) (PreH23 : (hi < modulus)) (PreH24 : (lo <= (hi + 1 ))) (PreH25 : (0 <= ans)) (PreH26 : (ans < modulus)) (PreH27 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH28 : (SearchState modulus values lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "mm" ) )) # Int  |-> mm_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nn_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < modulus))) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (values: (@list Z)) (modulus: Z) (nn_pre: Z) (mm_pre: Z) (input_pre: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (lo <= hi)) (PreH2 : (nn_pre = (Zlength (values)))) (PreH3 : (mm_pre = modulus)) (PreH4 : (1 <= modulus)) (PreH5 : (modulus <= 300000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 300000)) (PreH8 : (0 <= lo)) (PreH9 : (lo <= modulus)) (PreH10 : ((-1) <= hi)) (PreH11 : (hi < modulus)) (PreH12 : (lo <= (hi + 1 ))) (PreH13 : (0 <= ans)) (PreH14 : (ans < modulus)) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus)))) (PreH16 : (SearchState modulus values lo hi ans )),
  (IntArray.full input_pre nn_pre values )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> mm_pre)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= modulus) ”
  &&  “ (modulus <= 300000) ”
  &&  “ (1 <= nn_pre) ”
  &&  “ (nn_pre <= 300000) ”
  &&  “ ((Zlength (values)) = nn_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nn_pre)) -> ((0 <= (Znth j values 0)) /\ ((Znth j values 0) < modulus))) ”
  &&  “ (((lo + hi ) ÷ 2 ) < modulus) ”
  &&  “ (0 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (lo <= hi) ”
  &&  “ (nn_pre = (Zlength (values))) ”
  &&  “ (mm_pre = modulus) ”
  &&  “ (1 <= modulus) ”
  &&  “ (modulus <= 300000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 300000) ”
  &&  “ (0 <= lo) ”
  &&  “ (lo <= modulus) ”
  &&  “ ((-1) <= hi) ”
  &&  “ (hi < modulus) ”
  &&  “ (lo <= (hi + 1 )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans < modulus) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) < modulus))) ”
  &&  “ (SearchState modulus values lo hi ans ) ”
  &&  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "m" ) )) # Int  |-> modulus)
  **  ((( &( "a" ) )) # Ptr  |-> input_pre)
  **  (IntArray.full input_pre nn_pre values )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_feasible_safety_wit_1 : feasible_safety_wit_1.
Axiom proof_of_feasible_safety_wit_2 : feasible_safety_wit_2.
Axiom proof_of_feasible_safety_wit_3 : feasible_safety_wit_3.
Axiom proof_of_feasible_safety_wit_4 : feasible_safety_wit_4.
Axiom proof_of_feasible_safety_wit_5 : feasible_safety_wit_5.
Axiom proof_of_feasible_safety_wit_6 : feasible_safety_wit_6.
Axiom proof_of_feasible_safety_wit_7 : feasible_safety_wit_7.
Axiom proof_of_feasible_safety_wit_8 : feasible_safety_wit_8.
Axiom proof_of_feasible_safety_wit_9 : feasible_safety_wit_9.
Axiom proof_of_feasible_safety_wit_10 : feasible_safety_wit_10.
Axiom proof_of_feasible_safety_wit_11 : feasible_safety_wit_11.
Axiom proof_of_feasible_safety_wit_12 : feasible_safety_wit_12.
Axiom proof_of_feasible_safety_wit_13 : feasible_safety_wit_13.
Axiom proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Axiom proof_of_feasible_entail_wit_2_1 : feasible_entail_wit_2_1.
Axiom proof_of_feasible_entail_wit_2_2 : feasible_entail_wit_2_2.
Axiom proof_of_feasible_entail_wit_2_3 : feasible_entail_wit_2_3.
Axiom proof_of_feasible_entail_wit_2_4 : feasible_entail_wit_2_4.
Axiom proof_of_feasible_entail_wit_2_5 : feasible_entail_wit_2_5.
Axiom proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Axiom proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Axiom proof_of_feasible_partial_solve_wit_1 : feasible_partial_solve_wit_1.
Axiom proof_of_feasible_partial_solve_wit_2 : feasible_partial_solve_wit_2.
Axiom proof_of_feasible_partial_solve_wit_3 : feasible_partial_solve_wit_3.
Axiom proof_of_feasible_partial_solve_wit_4 : feasible_partial_solve_wit_4.
Axiom proof_of_feasible_partial_solve_wit_5 : feasible_partial_solve_wit_5.
Axiom proof_of_feasible_partial_solve_wit_6 : feasible_partial_solve_wit_6.
Axiom proof_of_feasible_partial_solve_wit_7 : feasible_partial_solve_wit_7.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
