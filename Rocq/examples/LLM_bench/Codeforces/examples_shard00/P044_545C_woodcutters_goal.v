From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P044_545C_woodcutters_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (trees)))) (PreH2 : ((Zlength (trees)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH4 : (Pre trees )) (PreH5 : (n_pre = (Zlength (trees)))) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_2 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  ((( &( "occupied" ) )) # Int64  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "occupied" ) )) # Int64  |-> (Znth 0 positions 0))
  **  ((( &( "answer" ) )) # Int  |-> 2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (n_pre = (Zlength (trees)))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (positions)) = n_pre)) (PreH5 : ((Zlength (heights)) = n_pre)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH7 : (Pre trees )) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (2 <= answer)) (PreH12 : (answer <= (i + 1 ))) (PreH13 : (PrefixFellingState trees i occupied answer )),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
  **  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (n_pre = (Zlength (trees)))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (positions)) = n_pre)) (PreH5 : ((Zlength (heights)) = n_pre)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH7 : (Pre trees )) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (2 <= answer)) (PreH12 : (answer <= (i + 1 ))) (PreH13 : (PrefixFellingState trees i occupied answer )),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
  **  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i positions 0) - (Znth i heights 0) )) ”
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i positions 0) - (Znth i heights 0) )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ ((INT64_MIN) <= ((Znth i positions 0) - (Znth i heights 0) )) ”
.

Definition solver_safety_wit_8 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) > occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ ((answer + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (answer + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i positions 0) + (Znth i heights 0) )) ”
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i positions 0) + (Znth i heights 0) )) ”
).

Definition solver_safety_wit_10_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ ((INT64_MIN) <= ((Znth i positions 0) + (Znth i heights 0) )) ”
.

Definition solver_safety_wit_11 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ ((answer + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (answer + 1 )) ”
.

Definition solver_safety_wit_13 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i positions 0) + (Znth i heights 0) )) ”
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i positions 0) + (Znth i heights 0) )) ”
).

Definition solver_safety_wit_13_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "occupied" ) )) # Int64  |-> occupied)
|--
  “ ((INT64_MIN) <= ((Znth i positions 0) + (Znth i heights 0) )) ”
.

Definition solver_safety_wit_14 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) > occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "occupied" ) )) # Int64  |-> (Znth i positions 0))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "occupied" ) )) # Int64  |-> ((Znth i positions 0) + (Znth i heights 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) >= (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "occupied" ) )) # Int64  |-> (Znth i positions 0))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre - 1 )) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= (1 + 1 )) ”
  &&  “ (PrefixFellingState trees 1 (Znth 0 positions 0) 2 ) ”
  &&  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  TT && emp 
|--
  “ (PrefixFellingState trees 1 (Znth 0 positions 0) 2 ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  (PrefixFellingState trees 1 (Znth 0 positions 0) 2 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))
.

Definition solver_entail_wit_2_1 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) > occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (2 <= (answer + 1 )) ”
  &&  “ ((answer + 1 ) <= ((i + 1 ) + 1 )) ”
  &&  “ (PrefixFellingState trees (i + 1 ) (Znth i positions 0) (answer + 1 ) ) ”
  &&  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) > occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  TT && emp 
|--
  “ (PrefixFellingState trees (i + 1 ) (Znth i positions 0) (answer + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) > occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (PrefixFellingState trees (i + 1 ) (Znth i positions 0) (answer + 1 ) )
.

Definition solver_entail_wit_2_2 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
|--
  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (2 <= (answer + 1 )) ”
  &&  “ ((answer + 1 ) <= ((i + 1 ) + 1 )) ”
  &&  “ (PrefixFellingState trees (i + 1 ) ((Znth i positions 0) + (Znth i heights 0) ) (answer + 1 ) ) ”
  &&  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  TT && emp 
|--
  “ (PrefixFellingState trees (i + 1 ) ((Znth i positions 0) + (Znth i heights 0) ) (answer + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (PrefixFellingState trees (i + 1 ) ((Znth i positions 0) + (Znth i heights 0) ) (answer + 1 ) )
.

Definition solver_entail_wit_2_3 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) >= (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= ((i + 1 ) + 1 )) ”
  &&  “ (PrefixFellingState trees (i + 1 ) (Znth i positions 0) answer ) ”
  &&  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) >= (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  TT && emp 
|--
  “ (PrefixFellingState trees (i + 1 ) (Znth i positions 0) answer ) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) >= (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (PrefixFellingState trees (i + 1 ) (Znth i positions 0) answer )
.

Definition solver_return_wit_1 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (Spec trees answer ) ”
  &&  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  TT && emp 
|--
  “ (Spec trees answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Spec trees answer )
.

Definition solver_return_wit_2 :=
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre <= 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (Spec trees n_pre ) ”
  &&  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
) \/
(
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre <= 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  TT && emp 
|--
  “ (Spec trees n_pre ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre <= 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  (Spec trees n_pre )
.

Definition solver_partial_solve_wit_1 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (1 <= (Zlength (trees)))) (PreH3 : ((Zlength (trees)) <= 100000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH5 : (Pre trees )) (PreH6 : (n_pre = (Zlength (trees)))) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0))))),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (n_pre > 2) ”
  &&  “ (1 <= (Zlength (trees))) ”
  &&  “ ((Zlength (trees)) <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (trees)))) -> (((1 <= (fst ((Znth i trees __default__Prod_Z_Z)))) /\ ((fst ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth i trees __default__Prod_Z_Z)))) /\ ((snd ((Znth i trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((fst ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 positions 0)) /\ ((snd ((Znth i_2 trees __default__Prod_Z_Z))) = (Znth i_2 heights 0)))) ”
  &&  (((x_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 positions 0))
  **  (Int64Array.missing_i x_pre 0 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
.

Definition solver_partial_solve_wit_2 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((x_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i positions 0))
  **  (Int64Array.missing_i x_pre i 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
.

Definition solver_partial_solve_wit_3 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (trees)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (positions)) = n_pre)) (PreH6 : ((Zlength (heights)) = n_pre)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH8 : (Pre trees )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (2 <= answer)) (PreH13 : (answer <= (i + 1 ))) (PreH14 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((h_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i heights 0))
  **  (Int64Array.missing_i h_pre i 0 n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
.

Definition solver_partial_solve_wit_4 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) > occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) > occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((x_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i positions 0))
  **  (Int64Array.missing_i x_pre i 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
.

Definition solver_partial_solve_wit_5 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) <= occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((x_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i positions 0))
  **  (Int64Array.missing_i x_pre i 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
.

Definition solver_partial_solve_wit_6 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) <= occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((h_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i heights 0))
  **  (Int64Array.missing_i h_pre i 0 n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
.

Definition solver_partial_solve_wit_7 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (trees)))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (positions)) = n_pre)) (PreH7 : ((Zlength (heights)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH9 : (Pre trees )) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (2 <= answer)) (PreH14 : (answer <= (i + 1 ))) (PreH15 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full h_pre n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
|--
  “ (((Znth i positions 0) - (Znth i heights 0) ) <= occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((x_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i + 1 ) positions 0))
  **  (Int64Array.missing_i x_pre (i + 1 ) 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
.

Definition solver_partial_solve_wit_8 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0)) ”
  &&  “ (((Znth i positions 0) - (Znth i heights 0) ) <= occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((x_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i positions 0))
  **  (Int64Array.missing_i x_pre i 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
.

Definition solver_partial_solve_wit_9 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) < (Znth (i + 1 ) positions 0)) ”
  &&  “ (((Znth i positions 0) - (Znth i heights 0) ) <= occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((h_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i heights 0))
  **  (Int64Array.missing_i h_pre i 0 n_pre heights )
  **  (Int64Array.full x_pre n_pre positions )
.

Definition solver_partial_solve_wit_10 :=
forall (heights: (@list Z)) (positions: (@list Z)) (trees: (@list (Z * Z))) (x_pre: Z) (h_pre: Z) (n_pre: Z) (occupied: Z) (answer: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (((Znth i positions 0) + (Znth i heights 0) ) >= (Znth (i + 1 ) positions 0))) (PreH2 : (((Znth i positions 0) - (Znth i heights 0) ) <= occupied)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (trees)))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (positions)) = n_pre)) (PreH8 : ((Zlength (heights)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000))))) (PreH10 : (Pre trees )) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0))))) (PreH12 : (1 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (2 <= answer)) (PreH15 : (answer <= (i + 1 ))) (PreH16 : (PrefixFellingState trees i occupied answer )),
  (Int64Array.full x_pre n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
|--
  “ (((Znth i positions 0) + (Znth i heights 0) ) >= (Znth (i + 1 ) positions 0)) ”
  &&  “ (((Znth i positions 0) - (Znth i heights 0) ) <= occupied) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (trees))) ”
  &&  “ (3 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (positions)) = n_pre) ”
  &&  “ ((Zlength (heights)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((1 <= (fst ((Znth j trees __default__Prod_Z_Z)))) /\ ((fst ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)) /\ ((1 <= (snd ((Znth j trees __default__Prod_Z_Z)))) /\ ((snd ((Znth j trees __default__Prod_Z_Z))) <= 1000000000)))) ”
  &&  “ (Pre trees ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((fst ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 positions 0)) /\ ((snd ((Znth j_2 trees __default__Prod_Z_Z))) = (Znth j_2 heights 0)))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (2 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (PrefixFellingState trees i occupied answer ) ”
  &&  (((x_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i positions 0))
  **  (Int64Array.missing_i x_pre i 0 n_pre positions )
  **  (Int64Array.full h_pre n_pre heights )
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
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.

End VC_Correct.
