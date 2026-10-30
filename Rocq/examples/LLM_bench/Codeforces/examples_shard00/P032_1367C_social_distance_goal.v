From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P032_1367C_social_distance_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (seats)))) (PreH4 : ((Zlength (seats)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH6 : (Pre k_pre seats )),
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (((-k_pre) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((-k_pre) - 1 )) ”
.

Definition solver_safety_wit_2 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (seats)))) (PreH4 : ((Zlength (seats)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH6 : (Pre k_pre seats )),
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (k_pre <> (INT_MIN)) ”
.

Definition solver_safety_wit_3 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (seats)))) (PreH4 : ((Zlength (seats)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH6 : (Pre k_pre seats )),
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (seats)))) (PreH4 : ((Zlength (seats)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH6 : (Pre k_pre seats )),
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (seats)))) (PreH5 : ((Zlength (seats)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH7 : (Pre k_pre seats )),
  ((( &( "nearest" ) )) # Int  |->_)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "next" ) )) # Ptr  |-> retval)
  **  ((( &( "last" ) )) # Int  |-> ((-k_pre) - 1 ))
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ ((n_pre + k_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre + k_pre )) ”
.

Definition solver_safety_wit_6 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (seats)))) (PreH5 : ((Zlength (seats)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH7 : (Pre k_pre seats )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nearest" ) )) # Int  |-> (n_pre + k_pre ))
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "next" ) )) # Ptr  |-> retval)
  **  ((( &( "last" ) )) # Int  |-> ((-k_pre) - 1 ))
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (seats)))) (PreH5 : ((Zlength (seats)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH7 : (Pre k_pre seats )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nearest" ) )) # Int  |-> (n_pre + k_pre ))
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "next" ) )) # Ptr  |-> retval)
  **  ((( &( "last" ) )) # Int  |-> ((-k_pre) - 1 ))
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH6 : (Pre k_pre seats )) (PreH7 : (answer = 0)) (PreH8 : (last = ((-k_pre) - 1 ))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= nearest)) (PreH12 : (nearest <= (n_pre + k_pre ))) (PreH13 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH14 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (i >= 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (answer = 0)) (PreH9 : (last = ((-k_pre) - 1 ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= nearest)) (PreH13 : (nearest <= (n_pre + k_pre ))) (PreH14 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH15 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_10 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (answer = 0)) (PreH10 : (last = ((-k_pre) - 1 ))) (PreH11 : ((-1) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= nearest)) (PreH14 : (nearest <= (n_pre + k_pre ))) (PreH15 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH16 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (IntArray.undef_seg next 0 i )
  **  (((next + (i * sizeof(INT)))) # Int  |-> i)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nearest" ) )) # Int  |-> i)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (answer = 0)) (PreH10 : (last = ((-k_pre) - 1 ))) (PreH11 : ((-1) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= nearest)) (PreH14 : (nearest <= (n_pre + k_pre ))) (PreH15 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH16 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (IntArray.undef_seg next 0 i )
  **  (((next + (i * sizeof(INT)))) # Int  |-> nearest)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next_values: (@list Z)) (answer: Z) (last: Z) (nearest: Z) (next: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH6 : (Pre k_pre seats )) (PreH7 : (answer = 0)) (PreH8 : (last = ((-k_pre) - 1 ))) (PreH9 : (0 <= nearest)) (PreH10 : (nearest <= (n_pre + k_pre ))) (PreH11 : (RightNearest seats k_pre 0 nearest )) (PreH12 : (RightNearestSuffix seats k_pre 0 next_values )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.full next n_pre next_values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= i)) (PreH12 : (((-k_pre) - 1 ) <= last)) (PreH13 : (last < i)) (PreH14 : (0 <= nearest)) (PreH15 : (nearest <= (n_pre + k_pre ))) (PreH16 : (RightNearest seats k_pre 0 nearest )) (PreH17 : (PrefixPlacementState seats k_pre i last answer )) (PreH18 : (RightNearestSuffix seats k_pre 0 next_values )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.full next n_pre next_values )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_14 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= i)) (PreH13 : (((-k_pre) - 1 ) <= last)) (PreH14 : (last < i)) (PreH15 : (0 <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre 0 nearest )) (PreH18 : (PrefixPlacementState seats k_pre i last answer )) (PreH19 : (RightNearestSuffix seats k_pre 0 next_values )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.full next n_pre next_values )
|--
  “ ((i - last ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - last )) ”
.

Definition solver_safety_wit_15 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) > k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ (((Znth i next_values 0) - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i next_values 0) - i )) ”
) \/
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) > k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ (((Znth i next_values 0) - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i next_values 0) - i )) ”
).

Definition solver_safety_wit_15_split_goal_1 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) > k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ (((Znth i next_values 0) - i ) <= INT_MAX) ”
.

Definition solver_safety_wit_15_split_goal_2 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) > k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ ((INT_MIN) <= ((Znth i next_values 0) - i )) ”
.

Definition solver_safety_wit_16 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values 0) - i ) > k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ ((answer + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (answer + 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values 0) - i ) > k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  ((( &( "last" ) )) # Int  |-> i)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) <= k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.full next n_pre next_values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values 0) - i ) <= k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values )),
  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= i)) (PreH13 : (((-k_pre) - 1 ) <= last)) (PreH14 : (last < i)) (PreH15 : (0 <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre 0 nearest )) (PreH18 : (PrefixPlacementState seats k_pre i last answer )) (PreH19 : (RightNearestSuffix seats k_pre 0 next_values )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "last" ) )) # Int  |-> i)
  **  ((( &( "nearest" ) )) # Int  |-> nearest)
  **  ((( &( "next" ) )) # Ptr  |-> next)
  **  (IntArray.full next n_pre next_values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (seats)))) (PreH5 : ((Zlength (seats)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH7 : (Pre k_pre seats )),
  (IntArray.undef_full retval n_pre )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  EX (suffix: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 = 0) ”
  &&  “ (((-k_pre) - 1 ) = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ (((n_pre - 1 ) + 1 ) <= (n_pre + k_pre )) ”
  &&  “ ((n_pre + k_pre ) <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre ((n_pre - 1 ) + 1 ) (n_pre + k_pre ) ) ”
  &&  “ (RightNearestSuffix seats k_pre ((n_pre - 1 ) + 1 ) suffix ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg retval 0 ((n_pre - 1 ) + 1 ) )
  **  (IntArray.seg retval ((n_pre - 1 ) + 1 ) n_pre suffix )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (seats)))) (PreH5 : ((Zlength (seats)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH7 : (Pre k_pre seats )),
  (IntArray.undef_full retval n_pre )
|--
  EX (suffix: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ ((-1) <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ (((n_pre - 1 ) + 1 ) <= (n_pre + k_pre )) ”
  &&  “ ((n_pre + k_pre ) <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre ((n_pre - 1 ) + 1 ) (n_pre + k_pre ) ) ”
  &&  “ (RightNearestSuffix seats k_pre ((n_pre - 1 ) + 1 ) suffix ) ”
  &&  (IntArray.undef_seg retval 0 ((n_pre - 1 ) + 1 ) )
  **  (IntArray.seg retval ((n_pre - 1 ) + 1 ) n_pre suffix )
).

Definition solver_entail_wit_2_1 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix_2: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (answer = 0)) (PreH10 : (last = ((-k_pre) - 1 ))) (PreH11 : ((-1) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= nearest)) (PreH14 : (nearest <= (n_pre + k_pre ))) (PreH15 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH16 : (RightNearestSuffix seats k_pre (i + 1 ) suffix_2 )),
  (IntArray.undef_seg next 0 i )
  **  (((next + (i * sizeof(INT)))) # Int  |-> i)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix_2 )
|--
  EX (suffix: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (((i - 1 ) + 1 ) <= i) ”
  &&  “ (i <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre ((i - 1 ) + 1 ) i ) ”
  &&  “ (RightNearestSuffix seats k_pre ((i - 1 ) + 1 ) suffix ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 ((i - 1 ) + 1 ) )
  **  (IntArray.seg next ((i - 1 ) + 1 ) n_pre suffix )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next: Z) (suffix_2: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : (i >= 0)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (answer = 0)) (PreH12 : (last = ((-k_pre) - 1 ))) (PreH13 : ((-1) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1 ) <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH18 : (RightNearestSuffix seats k_pre (i + 1 ) suffix_2 )),
  (((next + (i * sizeof(INT)))) # Int  |-> i)
  **  (IntArray.seg next (i + 1 ) n_pre suffix_2 )
|--
  EX (suffix: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (((i - 1 ) + 1 ) <= i) ”
  &&  “ (i <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre ((i - 1 ) + 1 ) i ) ”
  &&  “ (RightNearestSuffix seats k_pre ((i - 1 ) + 1 ) suffix ) ”
  &&  (IntArray.seg next ((i - 1 ) + 1 ) n_pre suffix )
).

Definition solver_entail_wit_2_2 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix_2: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (answer = 0)) (PreH10 : (last = ((-k_pre) - 1 ))) (PreH11 : ((-1) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= nearest)) (PreH14 : (nearest <= (n_pre + k_pre ))) (PreH15 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH16 : (RightNearestSuffix seats k_pre (i + 1 ) suffix_2 )),
  (IntArray.undef_seg next 0 i )
  **  (((next + (i * sizeof(INT)))) # Int  |-> nearest)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix_2 )
|--
  EX (suffix: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (((i - 1 ) + 1 ) <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre ((i - 1 ) + 1 ) nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre ((i - 1 ) + 1 ) suffix ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 ((i - 1 ) + 1 ) )
  **  (IntArray.seg next ((i - 1 ) + 1 ) n_pre suffix )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next: Z) (suffix_2: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (nearest <= INT_MAX)) (PreH2 : (nearest >= INT_MIN)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i >= 0)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (answer = 0)) (PreH12 : (last = ((-k_pre) - 1 ))) (PreH13 : ((-1) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1 ) <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH18 : (RightNearestSuffix seats k_pre (i + 1 ) suffix_2 )),
  (((next + (i * sizeof(INT)))) # Int  |-> nearest)
  **  (IntArray.seg next (i + 1 ) n_pre suffix_2 )
|--
  EX (suffix: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (((i - 1 ) + 1 ) <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre ((i - 1 ) + 1 ) nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre ((i - 1 ) + 1 ) suffix ) ”
  &&  (IntArray.seg next ((i - 1 ) + 1 ) n_pre suffix )
).

Definition solver_entail_wit_3 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (i < 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 seats 0) = 48) \/ ((Znth j_2 seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (answer = 0)) (PreH9 : (last = ((-k_pre) - 1 ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= nearest)) (PreH13 : (nearest <= (n_pre + k_pre ))) (PreH14 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH15 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (i < 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 seats 0) = 48) \/ ((Znth j_2 seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (answer = 0)) (PreH9 : (last = ((-k_pre) - 1 ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= nearest)) (PreH13 : (nearest <= (n_pre + k_pre ))) (PreH14 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH15 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (IntArray.full next n_pre next_values )
).

Definition solver_entail_wit_4 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (answer: Z) (last: Z) (nearest: Z) (next: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 seats 0) = 48) \/ ((Znth j_2 seats 0) = 49)))) (PreH6 : (Pre k_pre seats )) (PreH7 : (answer = 0)) (PreH8 : (last = ((-k_pre) - 1 ))) (PreH9 : (0 <= nearest)) (PreH10 : (nearest <= (n_pre + k_pre ))) (PreH11 : (RightNearest seats k_pre 0 nearest )) (PreH12 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values_2 )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= 0) ”
  &&  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < 0) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre 0 last answer ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (answer: Z) (last: Z) (nearest: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 seats 0) = 48) \/ ((Znth j_2 seats 0) = 49)))) (PreH6 : (Pre k_pre seats )) (PreH7 : (answer = 0)) (PreH8 : (last = ((-k_pre) - 1 ))) (PreH9 : (0 <= nearest)) (PreH10 : (nearest <= (n_pre + k_pre ))) (PreH11 : (RightNearest seats k_pre 0 nearest )) (PreH12 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  TT && emp 
|--
  “ (PrefixPlacementState seats k_pre 0 ((-k_pre) - 1 ) 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (answer: Z) (last: Z) (nearest: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 seats 0) = 48) \/ ((Znth j_2 seats 0) = 49)))) (PreH6 : (Pre k_pre seats )) (PreH7 : (answer = 0)) (PreH8 : (last = ((-k_pre) - 1 ))) (PreH9 : (0 <= nearest)) (PreH10 : (nearest <= (n_pre + k_pre ))) (PreH11 : (RightNearest seats k_pre 0 nearest )) (PreH12 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (PrefixPlacementState seats k_pre 0 ((-k_pre) - 1 ) 0 )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (answer: Z) (last: Z) (nearest: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 seats 0) = 48) \/ ((Znth j_2 seats 0) = 49)))) (PreH6 : (Pre k_pre seats )) (PreH7 : (answer = 0)) (PreH8 : (last = ((-k_pre) - 1 ))) (PreH9 : (0 <= nearest)) (PreH10 : (nearest <= (n_pre + k_pre ))) (PreH11 : (RightNearest seats k_pre 0 nearest )) (PreH12 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))
.

Definition solver_entail_wit_5_1 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values_2 0) - i ) > k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (IntArray.full next n_pre next_values_2 )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (answer + 1 )) ”
  &&  “ ((answer + 1 ) <= (i + 1 )) ”
  &&  “ (((-k_pre) - 1 ) <= i) ”
  &&  “ (i < (i + 1 )) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre (i + 1 ) i (answer + 1 ) ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values_2 0) - i ) > k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  TT && emp 
|--
  “ (PrefixPlacementState seats k_pre (i + 1 ) i (answer + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values_2 0) - i ) > k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (PrefixPlacementState seats k_pre (i + 1 ) i (answer + 1 ) )
.

Definition solver_entail_wit_5_2 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) <= k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values_2 )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < (i + 1 )) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre (i + 1 ) last answer ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) <= k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  TT && emp 
|--
  “ (PrefixPlacementState seats k_pre (i + 1 ) last answer ) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) <= k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (PrefixPlacementState seats k_pre (i + 1 ) last answer )
.

Definition solver_entail_wit_5_3 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values_2 0) - i ) <= k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (IntArray.full next n_pre next_values_2 )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < (i + 1 )) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre (i + 1 ) last answer ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values_2 0) - i ) <= k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  TT && emp 
|--
  “ (PrefixPlacementState seats k_pre (i + 1 ) last answer ) ”
  &&  emp
).

Definition solver_entail_wit_5_3_split_goal_1 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (((Znth i next_values_2 0) - i ) <= k_pre)) (PreH2 : ((i - last ) > k_pre)) (PreH3 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (seats)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH10 : (Pre k_pre seats )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= i)) (PreH15 : (((-k_pre) - 1 ) <= last)) (PreH16 : (last < i)) (PreH17 : (0 <= nearest)) (PreH18 : (nearest <= (n_pre + k_pre ))) (PreH19 : (RightNearest seats k_pre 0 nearest )) (PreH20 : (PrefixPlacementState seats k_pre i last answer )) (PreH21 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (PrefixPlacementState seats k_pre (i + 1 ) last answer )
.

Definition solver_entail_wit_5_4 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= i)) (PreH13 : (((-k_pre) - 1 ) <= last)) (PreH14 : (last < i)) (PreH15 : (0 <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre 0 nearest )) (PreH18 : (PrefixPlacementState seats k_pre i last answer )) (PreH19 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values_2 )
|--
  EX (next_values: (@list Z)),
  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (i + 1 )) ”
  &&  “ (((-k_pre) - 1 ) <= i) ”
  &&  “ (i < (i + 1 )) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre (i + 1 ) i answer ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= i)) (PreH13 : (((-k_pre) - 1 ) <= last)) (PreH14 : (last < i)) (PreH15 : (0 <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre 0 nearest )) (PreH18 : (PrefixPlacementState seats k_pre i last answer )) (PreH19 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  TT && emp 
|--
  “ (PrefixPlacementState seats k_pre (i + 1 ) i answer ) ”
  &&  emp
).

Definition solver_entail_wit_5_4_split_goal_1 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= i)) (PreH13 : (((-k_pre) - 1 ) <= last)) (PreH14 : (last < i)) (PreH15 : (0 <= nearest)) (PreH16 : (nearest <= (n_pre + k_pre ))) (PreH17 : (RightNearest seats k_pre 0 nearest )) (PreH18 : (PrefixPlacementState seats k_pre i last answer )) (PreH19 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (PrefixPlacementState seats k_pre (i + 1 ) i answer )
.

Definition solver_entail_wit_6 :=
(
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= i)) (PreH12 : (((-k_pre) - 1 ) <= last)) (PreH13 : (last < i)) (PreH14 : (0 <= nearest)) (PreH15 : (nearest <= (n_pre + k_pre ))) (PreH16 : (RightNearest seats k_pre 0 nearest )) (PreH17 : (PrefixPlacementState seats k_pre i last answer )) (PreH18 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values_2 )
|--
  EX (next_values: (@list Z)),
  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < n_pre) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre n_pre last answer ) ”
  &&  “ (Spec k_pre seats answer ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
) \/
(
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= i)) (PreH12 : (((-k_pre) - 1 ) <= last)) (PreH13 : (last < i)) (PreH14 : (0 <= nearest)) (PreH15 : (nearest <= (n_pre + k_pre ))) (PreH16 : (RightNearest seats k_pre 0 nearest )) (PreH17 : (PrefixPlacementState seats k_pre i last answer )) (PreH18 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  TT && emp 
|--
  “ (Spec k_pre seats answer ) ”
  &&  “ (PrefixPlacementState seats k_pre n_pre last answer ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= i)) (PreH12 : (((-k_pre) - 1 ) <= last)) (PreH13 : (last < i)) (PreH14 : (0 <= nearest)) (PreH15 : (nearest <= (n_pre + k_pre ))) (PreH16 : (RightNearest seats k_pre 0 nearest )) (PreH17 : (PrefixPlacementState seats k_pre i last answer )) (PreH18 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (Spec k_pre seats answer )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (seats: (@list Z)) (n_pre: Z) (k_pre: Z) (next_values_2: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= i)) (PreH12 : (((-k_pre) - 1 ) <= last)) (PreH13 : (last < i)) (PreH14 : (0 <= nearest)) (PreH15 : (nearest <= (n_pre + k_pre ))) (PreH16 : (RightNearest seats k_pre 0 nearest )) (PreH17 : (PrefixPlacementState seats k_pre i last answer )) (PreH18 : (RightNearestSuffix seats k_pre 0 next_values_2 )),
  (PrefixPlacementState seats k_pre n_pre last answer )
.

Definition solver_return_wit_1 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (last: Z) (nearest: Z) (answer: Z) (PreH1 : (((-k_pre) - 1 ) <= last)) (PreH2 : (last < n_pre)) (PreH3 : (0 <= nearest)) (PreH4 : (nearest <= (n_pre + k_pre ))) (PreH5 : (RightNearest seats k_pre 0 nearest )) (PreH6 : (PrefixPlacementState seats k_pre n_pre last answer )) (PreH7 : (Spec k_pre seats answer )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec k_pre seats answer ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_1_pure :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (seats)))) (PreH4 : ((Zlength (seats)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH6 : (Pre k_pre seats )),
  ((( &( "next" ) )) # Ptr  |->_)
  **  ((( &( "last" ) )) # Int  |-> ((-k_pre) - 1 ))
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (n_pre = (Zlength (seats)))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (seats)))) (PreH4 : ((Zlength (seats)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49)))) (PreH6 : (Pre k_pre seats )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
  &&  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (seats))) ”
  &&  “ ((Zlength (seats)) <= 200000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (seats)))) -> (((Znth i seats 0) = 48) \/ ((Znth i seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : (i >= 0)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (answer = 0)) (PreH9 : (last = ((-k_pre) - 1 ))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= nearest)) (PreH13 : (nearest <= (n_pre + k_pre ))) (PreH14 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH15 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ (i >= 0) ”
  &&  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre (i + 1 ) nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre (i + 1 ) suffix ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (seats) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
.

Definition solver_partial_solve_wit_3 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (answer = 0)) (PreH10 : (last = ((-k_pre) - 1 ))) (PreH11 : ((-1) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= nearest)) (PreH14 : (nearest <= (n_pre + k_pre ))) (PreH15 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH16 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) = 49) ”
  &&  “ (i >= 0) ”
  &&  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre (i + 1 ) nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre (i + 1 ) suffix ) ”
  &&  (((next + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i next i 0 (i + 1 ) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
.

Definition solver_partial_solve_wit_4 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (suffix: (@list Z)) (nearest: Z) (i: Z) (last: Z) (answer: Z) (PreH1 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (seats)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH8 : (Pre k_pre seats )) (PreH9 : (answer = 0)) (PreH10 : (last = ((-k_pre) - 1 ))) (PreH11 : ((-1) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= nearest)) (PreH14 : (nearest <= (n_pre + k_pre ))) (PreH15 : (RightNearest seats k_pre (i + 1 ) nearest )) (PreH16 : (RightNearestSuffix seats k_pre (i + 1 ) suffix )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg next 0 (i + 1 ) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
|--
  “ ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49) ”
  &&  “ (i >= 0) ”
  &&  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (answer = 0) ”
  &&  “ (last = ((-k_pre) - 1 )) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre (i + 1 ) nearest ) ”
  &&  “ (RightNearestSuffix seats k_pre (i + 1 ) suffix ) ”
  &&  (((next + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i next i 0 (i + 1 ) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg next (i + 1 ) n_pre suffix )
.

Definition solver_partial_solve_wit_5 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (seats)))) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH7 : (Pre k_pre seats )) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= i)) (PreH12 : (((-k_pre) - 1 ) <= last)) (PreH13 : (last < i)) (PreH14 : (0 <= nearest)) (PreH15 : (nearest <= (n_pre + k_pre ))) (PreH16 : (RightNearest seats k_pre 0 nearest )) (PreH17 : (PrefixPlacementState seats k_pre i last answer )) (PreH18 : (RightNearestSuffix seats k_pre 0 next_values )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= i) ”
  &&  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < i) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre i last answer ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (seats) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
.

Definition solver_partial_solve_wit_6 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next: Z) (next_values: (@list Z)) (nearest: Z) (last: Z) (answer: Z) (i: Z) (PreH1 : ((i - last ) > k_pre)) (PreH2 : ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (seats)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49)))) (PreH9 : (Pre k_pre seats )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= i)) (PreH14 : (((-k_pre) - 1 ) <= last)) (PreH15 : (last < i)) (PreH16 : (0 <= nearest)) (PreH17 : (nearest <= (n_pre + k_pre ))) (PreH18 : (RightNearest seats k_pre 0 nearest )) (PreH19 : (PrefixPlacementState seats k_pre i last answer )) (PreH20 : (RightNearestSuffix seats k_pre 0 next_values )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
|--
  “ ((i - last ) > k_pre) ”
  &&  “ ((Znth i (app (seats) ((cons (0) ((@nil Z))))) 0) <> 49) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (seats))) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> (((Znth j seats 0) = 48) \/ ((Znth j seats 0) = 49))) ”
  &&  “ (Pre k_pre seats ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= i) ”
  &&  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < i) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre i last answer ) ”
  &&  “ (RightNearestSuffix seats k_pre 0 next_values ) ”
  &&  (((next + (i * sizeof(INT)))) # Int  |-> (Znth i next_values 0))
  **  (IntArray.missing_i next i 0 n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_7 :=
forall (seats: (@list Z)) (s_pre: Z) (n_pre: Z) (k_pre: Z) (next_values: (@list Z)) (last: Z) (nearest: Z) (answer: Z) (next: Z) (PreH1 : (((-k_pre) - 1 ) <= last)) (PreH2 : (last < n_pre)) (PreH3 : (0 <= nearest)) (PreH4 : (nearest <= (n_pre + k_pre ))) (PreH5 : (RightNearest seats k_pre 0 nearest )) (PreH6 : (PrefixPlacementState seats k_pre n_pre last answer )) (PreH7 : (Spec k_pre seats answer )),
  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full next n_pre next_values )
|--
  “ (((-k_pre) - 1 ) <= last) ”
  &&  “ (last < n_pre) ”
  &&  “ (0 <= nearest) ”
  &&  “ (nearest <= (n_pre + k_pre )) ”
  &&  “ (RightNearest seats k_pre 0 nearest ) ”
  &&  “ (PrefixPlacementState seats k_pre n_pre last answer ) ”
  &&  “ (Spec k_pre seats answer ) ”
  &&  (IntArray.full next n_pre next_values )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (seats) ((cons (0) ((@nil Z))))) )
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
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
