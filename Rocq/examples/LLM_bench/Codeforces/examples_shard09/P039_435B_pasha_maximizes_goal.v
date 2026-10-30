From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 19)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : ((Znth 0 digits 0) <> 48)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((48 <= (Znth i digits 0)) /\ ((Znth i digits 0) <= 57)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full d_pre (n_pre + 1 ) (app (digits) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 <= k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth 0 digits 0) <> 48)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH11 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (GreedyProgress digits k_pre cur i k )) (PreH15 : (GreedySelectionReady cur i k )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k )) (PreH16 : (GreedySelectionReady cur i k )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k )) (PreH16 : (GreedySelectionReady cur i k )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth 0 digits 0) <> 48)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH11 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (j <= ((i + k ) + 1 ))) (PreH17 : (i <= best)) (PreH18 : (best < j)) (PreH19 : (FirstMaximumPrefix cur i j best )) (PreH20 : (GreedyProgress digits k_pre cur i k )) (PreH21 : (GreedySelectionReady cur i k )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ ((j - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - i )) ”
.

Definition solver_safety_wit_6 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : ((Znth j (app (cur) ((cons (0) ((@nil Z))))) 0) > (Znth best (app (cur) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((j - i ) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : (0 < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : ((Znth 0 digits 0) <> 48)) (PreH12 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH13 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k ) + 1 ))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur i j best )) (PreH22 : (GreedyProgress digits k_pre cur i k )) (PreH23 : (GreedySelectionReady cur i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : ((Znth j (app (cur) ((cons (0) ((@nil Z))))) 0) <= (Znth best (app (cur) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((j - i ) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : (0 < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : ((Znth 0 digits 0) <> 48)) (PreH12 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH13 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k ) + 1 ))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur i j best )) (PreH22 : (GreedyProgress digits k_pre cur i k )) (PreH23 : (GreedySelectionReady cur i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (replace_Znth (j) ((Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0)) ((app (cur) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (replace_Znth (j) ((Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0)) ((app (cur) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (replace_Znth ((j - 1 )) ((Znth j (app (cur) ((cons (0) ((@nil Z))))) 0)) ((replace_Znth (j) ((Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0)) ((app (cur) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (replace_Znth ((j - 1 )) ((Znth j (app (cur) ((cons (0) ((@nil Z))))) 0)) ((replace_Znth (j) ((Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0)) ((app (cur) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "k" ) )) # Int  |-> (k - 1 ))
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 19)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : ((Znth 0 digits 0) <> 48)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((48 <= (Znth i digits 0)) /\ ((Znth i digits 0) <= 57)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (digits) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (GreedyProgress digits k_pre cur 0 k_pre ) ”
  &&  “ (GreedySelectionReady cur 0 k_pre ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 19)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : ((Znth 0 digits 0) <> 48)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((48 <= (Znth i digits 0)) /\ ((Znth i digits 0) <= 57)))),
  TT && emp 
|--
  EX (cur: (@list Z)),
  “ ((app (digits) ((cons (0) ((@nil Z))))) = (app (cur) ((cons (0) ((@nil Z)))))) ”
  &&  “ (k_pre <= k_pre) ”
  &&  “ ((Zlength (cur)) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (digits))) ”
  &&  “ (GreedyProgress digits k_pre cur 0 k_pre ) ”
  &&  “ (GreedySelectionReady cur 0 k_pre ) ”
  &&  emp
).

Definition solver_entail_wit_2 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits 0)) /\ ((Znth p_3 digits 0) <= 57)))) (PreH12 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 cur_2 0)) /\ ((Znth p_4 cur_2 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur_2 i k )) (PreH16 : (GreedySelectionReady cur_2 i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < k) ”
  &&  “ (k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((i + 1 ) <= ((i + k ) + 1 )) ”
  &&  “ (i <= i) ”
  &&  “ (i < (i + 1 )) ”
  &&  “ (FirstMaximumPrefix cur i (i + 1 ) i ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits 0)) /\ ((Znth p_3 digits 0) <= 57)))) (PreH12 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 cur_2 0)) /\ ((Znth p_4 cur_2 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur_2 i k )) (PreH16 : (GreedySelectionReady cur_2 i k )),
  TT && emp 
|--
  EX (cur: (@list Z)),
  “ ((app (cur_2) ((cons (0) ((@nil Z))))) = (app (cur) ((cons (0) ((@nil Z)))))) ”
  &&  “ (0 < k) ”
  &&  “ ((Zlength (cur)) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ ((i + 1 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (digits))) ”
  &&  “ ((i + 1 ) <= ((i + k ) + 1 )) ”
  &&  “ (i <= i) ”
  &&  “ (i < (i + 1 )) ”
  &&  “ (FirstMaximumPrefix cur i (i + 1 ) i ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  emp
).

Definition solver_entail_wit_3_1 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : ((Znth j (app (cur_2) ((cons (0) ((@nil Z))))) 0) > (Znth best (app (cur_2) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((j - i ) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : (0 < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth 0 digits 0) <> 48)) (PreH12 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH13 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 0)) /\ ((Znth p_2 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k ) + 1 ))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best )) (PreH22 : (GreedyProgress digits k_pre cur_2 i k )) (PreH23 : (GreedySelectionReady cur_2 i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < k) ”
  &&  “ (k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ ((j + 1 ) <= ((i + k ) + 1 )) ”
  &&  “ (i <= j) ”
  &&  “ (j < (j + 1 )) ”
  &&  “ (FirstMaximumPrefix cur i (j + 1 ) j ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : ((Znth j (app (cur_2) ((cons (0) ((@nil Z))))) 0) > (Znth best (app (cur_2) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((j - i ) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : (0 < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth 0 digits 0) <> 48)) (PreH12 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH13 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 0)) /\ ((Znth p_2 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k ) + 1 ))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best )) (PreH22 : (GreedyProgress digits k_pre cur_2 i k )) (PreH23 : (GreedySelectionReady cur_2 i k )),
  TT && emp 
|--
  EX (cur: (@list Z)),
  “ ((app (cur_2) ((cons (0) ((@nil Z))))) = (app (cur) ((cons (0) ((@nil Z)))))) ”
  &&  “ ((Zlength (cur)) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (digits))) ”
  &&  “ ((j + 1 ) <= ((i + k ) + 1 )) ”
  &&  “ (i <= j) ”
  &&  “ (j < (j + 1 )) ”
  &&  “ (FirstMaximumPrefix cur i (j + 1 ) j ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  emp
).

Definition solver_entail_wit_3_2 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : ((Znth j (app (cur_2) ((cons (0) ((@nil Z))))) 0) <= (Znth best (app (cur_2) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((j - i ) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : (0 < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth 0 digits 0) <> 48)) (PreH12 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH13 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 0)) /\ ((Znth p_2 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k ) + 1 ))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best )) (PreH22 : (GreedyProgress digits k_pre cur_2 i k )) (PreH23 : (GreedySelectionReady cur_2 i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < k) ”
  &&  “ (k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ ((j + 1 ) <= ((i + k ) + 1 )) ”
  &&  “ (i <= best) ”
  &&  “ (best < (j + 1 )) ”
  &&  “ (FirstMaximumPrefix cur i (j + 1 ) best ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : ((Znth j (app (cur_2) ((cons (0) ((@nil Z))))) 0) <= (Znth best (app (cur_2) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((j - i ) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : (0 < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth 0 digits 0) <> 48)) (PreH12 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH13 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 0)) /\ ((Znth p_2 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k ) + 1 ))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best )) (PreH22 : (GreedyProgress digits k_pre cur_2 i k )) (PreH23 : (GreedySelectionReady cur_2 i k )),
  TT && emp 
|--
  EX (cur: (@list Z)),
  “ ((app (cur_2) ((cons (0) ((@nil Z))))) = (app (cur) ((cons (0) ((@nil Z)))))) ”
  &&  “ ((Zlength (cur)) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (digits))) ”
  &&  “ ((j + 1 ) <= ((i + k ) + 1 )) ”
  &&  “ (best < (j + 1 )) ”
  &&  “ (FirstMaximumPrefix cur i (j + 1 ) best ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  emp
).

Definition solver_entail_wit_4_1 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur_2)) = n_pre)) (PreH9 : ((Znth 0 digits 0) <> 48)) (PreH10 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits 0)) /\ ((Znth p_4 digits 0) <= 57)))) (PreH11 : forall (p_5: Z), (((0 <= p_5) /\ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 0)) /\ ((Znth p_5 cur_2 0) <= 57)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (j <= ((i + k ) + 1 ))) (PreH17 : (i <= best)) (PreH18 : (best < j)) (PreH19 : (FirstMaximumPrefix cur_2 i j best )) (PreH20 : (GreedyProgress digits k_pre cur_2 i k )) (PreH21 : (GreedySelectionReady cur_2 i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)) (before: (@list Z)) (start_k: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= best) ”
  &&  “ (best <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - best ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) (best))) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur_2)) = n_pre)) (PreH9 : ((Znth 0 digits 0) <> 48)) (PreH10 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits 0)) /\ ((Znth p_4 digits 0) <= 57)))) (PreH11 : forall (p_5: Z), (((0 <= p_5) /\ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 0)) /\ ((Znth p_5 cur_2 0) <= 57)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (j <= ((i + k ) + 1 ))) (PreH17 : (i <= best)) (PreH18 : (best < j)) (PreH19 : (FirstMaximumPrefix cur_2 i j best )) (PreH20 : (GreedyProgress digits k_pre cur_2 i k )) (PreH21 : (GreedySelectionReady cur_2 i k )),
  TT && emp 
|--
  EX (before: (@list Z)) (start_k: Z),
  “ ((app (cur_2) ((cons (0) ((@nil Z))))) = (app ((move_left (before) (best) (best))) ((cons (0) ((@nil Z)))))) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ ((Zlength (before)) = (Zlength (digits))) ”
  &&  “ ((Zlength ((move_left (before) (best) (best)))) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < (Zlength (digits)))) -> ((48 <= (Znth p_3 (move_left (before) (best) (best)) 0)) /\ ((Znth p_3 (move_left (before) (best) (best)) 0) <= 57))) ”
  &&  “ (best <= best) ”
  &&  “ (best < (Zlength (digits))) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - best ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  emp
).

Definition solver_entail_wit_4_2 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : ((j - i ) > k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits 0)) /\ ((Znth p_4 digits 0) <= 57)))) (PreH12 : forall (p_5: Z), (((0 <= p_5) /\ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 0)) /\ ((Znth p_5 cur_2 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1 ) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k ) + 1 ))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur_2 i j best )) (PreH21 : (GreedyProgress digits k_pre cur_2 i k )) (PreH22 : (GreedySelectionReady cur_2 i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)) (before: (@list Z)) (start_k: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= best) ”
  &&  “ (best <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - best ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) (best))) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (k: Z) (PreH1 : ((j - i ) > k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits 0)) /\ ((Znth p_4 digits 0) <= 57)))) (PreH12 : forall (p_5: Z), (((0 <= p_5) /\ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 0)) /\ ((Znth p_5 cur_2 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1 ) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k ) + 1 ))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur_2 i j best )) (PreH21 : (GreedyProgress digits k_pre cur_2 i k )) (PreH22 : (GreedySelectionReady cur_2 i k )),
  TT && emp 
|--
  EX (before: (@list Z)) (start_k: Z),
  “ ((app (cur_2) ((cons (0) ((@nil Z))))) = (app ((move_left (before) (best) (best))) ((cons (0) ((@nil Z)))))) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ ((Zlength (before)) = (Zlength (digits))) ”
  &&  “ ((Zlength ((move_left (before) (best) (best)))) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < (Zlength (digits)))) -> ((48 <= (Znth p_3 (move_left (before) (best) (best)) 0)) /\ ((Znth p_3 (move_left (before) (best) (best)) 0) <= 57))) ”
  &&  “ (best <= best) ”
  &&  “ (best < (Zlength (digits))) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - best ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  emp
).

Definition solver_entail_wit_5 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (before_2: (@list Z)) (start_k_2: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k_2)) (PreH5 : (start_k_2 <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before_2)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before_2 0)) /\ ((Znth p_2 before_2 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur_2 0)) /\ ((Znth p_3 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k_2)) (PreH20 : (k = (start_k_2 - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k_2)) (PreH23 : (ReachableFirstMaximum before_2 i start_k_2 best )) (PreH24 : (GreedyProgress digits k_pre before_2 i start_k_2 )) (PreH25 : (GreedySelectionReady before_2 i start_k_2 )) (PreH26 : (GreedyExchangeClosure before_2 i start_k_2 best )) (PreH27 : (cur_2 = (move_left (before_2) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (replace_Znth ((j - 1 )) ((Znth j (app (cur_2) ((cons (0) ((@nil Z))))) 0)) ((replace_Znth (j) ((Znth (j - 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) 0)) ((app (cur_2) ((cons (0) ((@nil Z))))))))) )
|--
  EX (cur: (@list Z)) (before: (@list Z)) (start_k: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= (j - 1 )) ”
  &&  “ ((j - 1 ) <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ ((k - 1 ) = (start_k - (best - (j - 1 ) ) )) ”
  &&  “ (0 <= (k - 1 )) ”
  &&  “ ((k - 1 ) <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) ((j - 1 )))) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (before_2: (@list Z)) (start_k_2: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k_2)) (PreH5 : (start_k_2 <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before_2)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before_2 0)) /\ ((Znth p_2 before_2 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur_2 0)) /\ ((Znth p_3 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k_2)) (PreH20 : (k = (start_k_2 - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k_2)) (PreH23 : (ReachableFirstMaximum before_2 i start_k_2 best )) (PreH24 : (GreedyProgress digits k_pre before_2 i start_k_2 )) (PreH25 : (GreedySelectionReady before_2 i start_k_2 )) (PreH26 : (GreedyExchangeClosure before_2 i start_k_2 best )) (PreH27 : (cur_2 = (move_left (before_2) (best) (j)))),
  TT && emp 
|--
  EX (before: (@list Z)) (start_k: Z),
  “ ((replace_Znth ((j - 1 )) ((Znth j (app ((move_left (before_2) (best) (j))) ((cons (0) ((@nil Z))))) 0)) ((replace_Znth (j) ((Znth (j - 1 ) (app ((move_left (before_2) (best) (j))) ((cons (0) ((@nil Z))))) 0)) ((app ((move_left (before_2) (best) (j))) ((cons (0) ((@nil Z))))))))) = (app ((move_left (before) (best) ((j - 1 )))) ((cons (0) ((@nil Z)))))) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ ((Zlength (before)) = (Zlength (digits))) ”
  &&  “ ((Zlength ((move_left (before) (best) ((j - 1 ))))) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < (Zlength (digits)))) -> ((48 <= (Znth p_3 (move_left (before) (best) ((j - 1 ))) 0)) /\ ((Znth p_3 (move_left (before) (best) ((j - 1 ))) 0) <= 57))) ”
  &&  “ (i <= (j - 1 )) ”
  &&  “ ((j - 1 ) <= best) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (((start_k_2 - (best - j ) ) - 1 ) = (start_k - (best - (j - 1 ) ) )) ”
  &&  “ (0 <= ((start_k_2 - (best - j ) ) - 1 )) ”
  &&  “ (((start_k_2 - (best - j ) ) - 1 ) <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  emp
).

Definition solver_entail_wit_6 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits 0)) /\ ((Znth p_3 digits 0) <= 57)))) (PreH12 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 before 0)) /\ ((Znth p_4 before 0) <= 57)))) (PreH13 : forall (p_5: Z), (((0 <= p_5) /\ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 0)) /\ ((Znth p_5 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur_2 = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur_2) ((cons (0) ((@nil Z))))) )
|--
  EX (cur: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (GreedyProgress digits k_pre cur (i + 1 ) k ) ”
  &&  “ (GreedySelectionReady cur (i + 1 ) k ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur_2: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits 0)) /\ ((Znth p_3 digits 0) <= 57)))) (PreH12 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 < n_pre)) -> ((48 <= (Znth p_4 before 0)) /\ ((Znth p_4 before 0) <= 57)))) (PreH13 : forall (p_5: Z), (((0 <= p_5) /\ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 0)) /\ ((Znth p_5 cur_2 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur_2 = (move_left (before) (best) (j)))),
  TT && emp 
|--
  EX (cur: (@list Z)),
  “ ((app ((move_left (before) (best) (j))) ((cons (0) ((@nil Z))))) = (app (cur) ((cons (0) ((@nil Z)))))) ”
  &&  “ ((start_k - (best - j ) ) <= k_pre) ”
  &&  “ ((Zlength (cur)) = (Zlength (digits))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (digits))) ”
  &&  “ (GreedyProgress digits k_pre cur (i + 1 ) (start_k - (best - j ) ) ) ”
  &&  “ (GreedySelectionReady cur (i + 1 ) (start_k - (best - j ) ) ) ”
  &&  emp
).

Definition solver_return_wit_1 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 <= k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth 0 digits 0) <> 48)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH11 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (GreedyProgress digits k_pre cur i k )) (PreH15 : (GreedySelectionReady cur i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  EX (out: (@list Z)),
  “ (Spec digits k_pre out ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 <= k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth 0 digits 0) <> 48)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH11 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (GreedyProgress digits k_pre cur i k )) (PreH15 : (GreedySelectionReady cur i k )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ ((app (cur) ((cons (0) ((@nil Z))))) = (app (out) ((cons (0) ((@nil Z)))))) ”
  &&  “ (Spec digits k_pre out ) ”
  &&  emp
).

Definition solver_return_wit_2 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k )) (PreH16 : (GreedySelectionReady cur i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  EX (out: (@list Z)),
  “ (Spec digits k_pre out ) ”
  &&  (CharArray.full d_pre (n_pre + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (k_pre: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k )) (PreH16 : (GreedySelectionReady cur i k )),
  TT && emp 
|--
  EX (out: (@list Z)),
  “ ((app (cur) ((cons (0) ((@nil Z))))) = (app (out) ((cons (0) ((@nil Z)))))) ”
  &&  “ (Spec digits k_pre out ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : ((j - i ) <= k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1 ) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k ) + 1 ))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur i j best )) (PreH21 : (GreedyProgress digits k_pre cur i k )) (PreH22 : (GreedySelectionReady cur i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ ((j - i ) <= k) ”
  &&  “ (j < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < k) ”
  &&  “ (k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (j <= ((i + k ) + 1 )) ”
  &&  “ (i <= best) ”
  &&  “ (best < j) ”
  &&  “ (FirstMaximumPrefix cur i j best ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  (((d_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i d_pre j 0 (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (k: Z) (PreH1 : ((j - i ) <= k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : (0 < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1 ) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k ) + 1 ))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur i j best )) (PreH21 : (GreedyProgress digits k_pre cur i k )) (PreH22 : (GreedySelectionReady cur i k )),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ ((j - i ) <= k) ”
  &&  “ (j < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < k) ”
  &&  “ (k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur 0)) /\ ((Znth p_2 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (j <= ((i + k ) + 1 )) ”
  &&  “ (i <= best) ”
  &&  “ (best < j) ”
  &&  “ (FirstMaximumPrefix cur i j best ) ”
  &&  “ (GreedyProgress digits k_pre cur i k ) ”
  &&  “ (GreedySelectionReady cur i k ) ”
  &&  (((d_pre + (best * sizeof(CHAR)))) # Char  |-> (Znth best (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i d_pre best 0 (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_3 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ (j > i) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - j ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i d_pre j 0 (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_4 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ (j > i) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - j ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + ((j - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i d_pre (j - 1 ) 0 (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_5 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
|--
  “ (j > i) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - j ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i d_pre j 0 (n_pre + 1 ) (app (cur) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_6 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (k_pre: Z) (k: Z) (best: Z) (j: Z) (i: Z) (cur: (@list Z)) (before: (@list Z)) (start_k: Z) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : (0 < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth 0 digits 0) <> 48)) (PreH11 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57)))) (PreH12 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57)))) (PreH13 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57)))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i ) <= start_k)) (PreH20 : (k = (start_k - (best - j ) ))) (PreH21 : (0 <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best )) (PreH24 : (GreedyProgress digits k_pre before i start_k )) (PreH25 : (GreedySelectionReady before i start_k )) (PreH26 : (GreedyExchangeClosure before i start_k best )) (PreH27 : (cur = (move_left (before) (best) (j)))),
  (CharArray.full d_pre (n_pre + 1 ) (replace_Znth (j) ((Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0)) ((app (cur) ((cons (0) ((@nil Z))))))) )
|--
  “ (j > i) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 19) ”
  &&  “ (0 < start_k) ”
  &&  “ (start_k <= k_pre) ”
  &&  “ (k_pre <= 100) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ ((Zlength (before)) = n_pre) ”
  &&  “ ((Zlength (cur)) = n_pre) ”
  &&  “ ((Znth 0 digits 0) <> 48) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> ((48 <= (Znth p digits 0)) /\ ((Znth p digits 0) <= 57))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before 0)) /\ ((Znth p_2 before 0) <= 57))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur 0)) /\ ((Znth p_3 cur 0) <= 57))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= best) ”
  &&  “ (best < n_pre) ”
  &&  “ ((best - i ) <= start_k) ”
  &&  “ (k = (start_k - (best - j ) )) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= start_k) ”
  &&  “ (ReachableFirstMaximum before i start_k best ) ”
  &&  “ (GreedyProgress digits k_pre before i start_k ) ”
  &&  “ (GreedySelectionReady before i start_k ) ”
  &&  “ (GreedyExchangeClosure before i start_k best ) ”
  &&  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + ((j - 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i d_pre (j - 1 ) 0 (n_pre + 1 ) (replace_Znth (j) ((Znth (j - 1 ) (app (cur) ((cons (0) ((@nil Z))))) 0)) ((app (cur) ((cons (0) ((@nil Z))))))) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.

End VC_Correct.
