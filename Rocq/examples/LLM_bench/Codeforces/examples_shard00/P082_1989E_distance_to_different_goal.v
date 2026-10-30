From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
(
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ ((k_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre + 1 )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ ((k_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre + 1 )) ”
).

Definition solver_safety_wit_1_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ ((k_pre + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_1_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ ((INT_MIN) <= (k_pre + 1 )) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "pref" ) )) # Ptr  |->_)
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "dp" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "pref" ) )) # Ptr  |->_)
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "dp" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "dp" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "dp" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (k_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full retval_2 (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "pref" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "dp" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_12 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 )) ”
).

Definition solver_safety_wit_12_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_18 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) ((((Znth (((i - 1 ) * W ) + 1 ) pl 0) + 1 ) % ( 998244353 ) )) (pl)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (P082InitState n_pre k_pre i dl pl )) (PreH12 : (P082SemanticInit n_pre k_pre i dl pl )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_20 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (j <= k_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= (k_pre + 1 ))) (PreH11 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH12 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (W = (k_pre + 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))) (PreH11 : (0 <= ((n_pre + 1 ) * W ))) (PreH12 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH13 : (2 <= j)) (PreH14 : (j <= k_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH18 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (W = (k_pre + 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))) (PreH11 : (0 <= ((n_pre + 1 ) * W ))) (PreH12 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH13 : (2 <= j)) (PreH14 : (j <= k_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH18 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (W = (k_pre + 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))) (PreH11 : (0 <= ((n_pre + 1 ) * W ))) (PreH12 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH13 : (2 <= j)) (PreH14 : (j <= k_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH18 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (W = (k_pre + 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))) (PreH11 : (0 <= ((n_pre + 1 ) * W ))) (PreH12 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH13 : (2 <= j)) (PreH14 : (j <= k_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH18 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (W = (k_pre + 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))) (PreH11 : (0 <= ((n_pre + 1 ) * W ))) (PreH12 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH13 : (2 <= j)) (PreH14 : (j <= k_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH18 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_26 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) )) ”
).

Definition solver_safety_wit_26_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) )) ”
.

Definition solver_safety_wit_27 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((j - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_28 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition solver_safety_wit_29 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_30 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_31 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) )) ”
).

Definition solver_safety_wit_31_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_31_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) )) ”
.

Definition solver_safety_wit_32 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_33 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_34 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) )) ”
).

Definition solver_safety_wit_34_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_34_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) )) ”
.

Definition solver_safety_wit_35 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_38 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_39 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH3 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH6 : (j <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (j = k_pre)) (PreH9 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH12 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH13 : (i >= 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ False ”
.

Definition solver_safety_wit_40 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH3 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH6 : (j <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (j = k_pre)) (PreH9 : (i < 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (k_pre <= INT_MAX)) (PreH13 : (k_pre >= INT_MIN)) (PreH14 : (i <= n_pre)) (PreH15 : (W = (k_pre + 1 ))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= (Zmin (n_pre) (10)))) (PreH20 : (0 <= ((n_pre + 1 ) * W ))) (PreH21 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH22 : (2 <= j)) (PreH23 : (j <= k_pre)) (PreH24 : (1 <= i)) (PreH25 : (i <= (n_pre + 1 ))) (PreH26 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH27 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ False ”
.

Definition solver_safety_wit_41 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) )) ”
).

Definition solver_safety_wit_41_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_41_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) )) ”
.

Definition solver_safety_wit_42 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition solver_safety_wit_43 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_44 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_45 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 )) ”
).

Definition solver_safety_wit_45_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_45_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 )) ”
.

Definition solver_safety_wit_46 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_47 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_48 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_49 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_50 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_51 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 )) ”
).

Definition solver_safety_wit_51_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_51_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 )) ”
.

Definition solver_safety_wit_52 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_53 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_54 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_55 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_56 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_57 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 )) ”
).

Definition solver_safety_wit_57_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_57_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 )) ”
.

Definition solver_safety_wit_58 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_59 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_60 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_61 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_62 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_63 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 )) ”
).

Definition solver_safety_wit_63_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_63_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 )) ”
.

Definition solver_safety_wit_64 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_65 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_66 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_67 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_68 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_69 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
).

Definition solver_safety_wit_69_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_69_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
.

Definition solver_safety_wit_70 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_71 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_72 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_73 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_74 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
).

Definition solver_safety_wit_74_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_74_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
.

Definition solver_safety_wit_75 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_76 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_77 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_78 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_79 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
).

Definition solver_safety_wit_79_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_79_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
.

Definition solver_safety_wit_80 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_81 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_82 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_83 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_84 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
).

Definition solver_safety_wit_84_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_84_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) )) ”
.

Definition solver_safety_wit_85 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_86 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_87 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_safety_wit_88 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) % ( 998244353 ) )) (pl)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_89 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) % ( 998244353 ) )) (pl)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_90 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) % ( 998244353 ) )) (pl)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_91 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0) ) % ( 998244353 ) )) (pl)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_92 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= k_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH14 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_93 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= ((n_pre * W ) + k_pre ))) (PreH2 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (j > k_pre)) (PreH4 : (W = (k_pre + 1 ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= k_pre)) (PreH8 : (k_pre <= (Zmin (n_pre) (10)))) (PreH9 : (0 <= ((n_pre + 1 ) * W ))) (PreH10 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH11 : (2 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH14 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_94 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (n_pre < 2)) (PreH2 : (0 <= ((n_pre * W ) + k_pre ))) (PreH3 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH4 : (j > k_pre)) (PreH5 : (W = (k_pre + 1 ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= k_pre)) (PreH9 : (k_pre <= (Zmin (n_pre) (10)))) (PreH10 : (0 <= ((n_pre + 1 ) * W ))) (PreH11 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH12 : (2 <= j)) (PreH13 : (j <= (k_pre + 1 ))) (PreH14 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH15 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ False ”
.

Definition solver_safety_wit_95 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (((((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) ) <> (INT64_MIN)) \/ (998244353 <> (-1))) ”
  &&  “ (998244353 <> 0) ”
.

Definition solver_safety_wit_96 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) )) ”
).

Definition solver_safety_wit_96_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_96_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((INT64_MIN) <= (((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) )) ”
.

Definition solver_safety_wit_97 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((n_pre - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition solver_safety_wit_98 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) )) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) )) ”
).

Definition solver_safety_wit_98_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_98_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((INT64_MIN) <= ((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) )) ”
.

Definition solver_safety_wit_99 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((k_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k_pre - 1 )) ”
.

Definition solver_safety_wit_100 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ ((n_pre - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition solver_safety_wit_101 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_102 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_103 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_104 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (998244353 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 998244353) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (k_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))),
  (Int64Array.full retval_2 (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ ((k_pre + 1 ) = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  “ (((n_pre + 1 ) * (k_pre + 1 ) ) <= UINT_MAX) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre 1 dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre 1 dl pl ) ”
  &&  (Int64Array.full retval ((n_pre + 1 ) * (k_pre + 1 ) ) dl )
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (k_pre + 1 ) ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))),
  (Int64Array.full retval_2 (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  “ (((n_pre + 1 ) * (k_pre + 1 ) ) <= UINT_MAX) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre 1 dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre 1 dl pl ) ”
  &&  (Int64Array.full retval ((n_pre + 1 ) * (k_pre + 1 ) ) dl )
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (k_pre + 1 ) ) pl )
).

Definition solver_entail_wit_2 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (i <= n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (P082InitState n_pre k_pre i dl pl )) (PreH12 : (P082SemanticInit n_pre k_pre i dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((i * W ) + 1 )) ”
  &&  “ (((i * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((i - 1 ) * W ) + 1 )) ”
  &&  “ ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre i dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (W <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (W >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i <= n_pre)) (PreH10 : (W = (k_pre + 1 ))) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= (Zmin (n_pre) (10)))) (PreH15 : (0 <= ((n_pre + 1 ) * W ))) (PreH16 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i <= (n_pre + 1 ))) (PreH19 : (P082InitState n_pre k_pre i dl pl )) (PreH20 : (P082SemanticInit n_pre k_pre i dl pl )),
  TT && emp 
|--
  “ ((((i - 1 ) * (k_pre + 1 ) ) + 1 ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  “ (((i * (k_pre + 1 ) ) + 1 ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (W <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (W >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i <= n_pre)) (PreH10 : (W = (k_pre + 1 ))) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= (Zmin (n_pre) (10)))) (PreH15 : (0 <= ((n_pre + 1 ) * W ))) (PreH16 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i <= (n_pre + 1 ))) (PreH19 : (P082InitState n_pre k_pre i dl pl )) (PreH20 : (P082SemanticInit n_pre k_pre i dl pl )),
  ((((i - 1 ) * (k_pre + 1 ) ) + 1 ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (W <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (W >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i <= n_pre)) (PreH10 : (W = (k_pre + 1 ))) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= (Zmin (n_pre) (10)))) (PreH15 : (0 <= ((n_pre + 1 ) * W ))) (PreH16 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i <= (n_pre + 1 ))) (PreH19 : (P082InitState n_pre k_pre i dl pl )) (PreH20 : (P082SemanticInit n_pre k_pre i dl pl )),
  (((i * (k_pre + 1 ) ) + 1 ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_3 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH18 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) ((((Znth (((i - 1 ) * W ) + 1 ) pl_2 0) + 1 ) % ( 998244353 ) )) (pl_2)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl_2)) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre (i + 1 ) dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre (i + 1 ) dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH18 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticInit n_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) (1) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + 1 ) pl_2 0) + 1 ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  “ (P082InitState n_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) (1) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + 1 ) pl_2 0) + 1 ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH18 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  (P082SemanticInit n_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) (1) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + 1 ) pl_2 0) + 1 ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH18 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  (P082InitState n_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) (1) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + 1 )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + 1 ) pl_2 0) + 1 ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_4 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH12 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl_2 )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl_2 )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre 2 dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre 2 dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH12 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticColumns n_pre k_pre 2 dl_2 pl_2 ) ”
  &&  “ (P082ColumnsState n_pre k_pre 2 dl_2 pl_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH12 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  (P082SemanticColumns n_pre k_pre 2 dl_2 pl_2 )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (P082InitState n_pre k_pre i dl_2 pl_2 )) (PreH12 : (P082SemanticInit n_pre k_pre i dl_2 pl_2 )),
  (P082ColumnsState n_pre k_pre 2 dl_2 pl_2 )
.

Definition solver_entail_wit_5 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (j <= k_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= (k_pre + 1 ))) (PreH11 : (P082ColumnsState n_pre k_pre j dl_2 pl_2 )) (PreH12 : (P082SemanticColumns n_pre k_pre j dl_2 pl_2 )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl_2 )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl_2 )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j 1 dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j 1 dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (j <= k_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= (k_pre + 1 ))) (PreH11 : (P082ColumnsState n_pre k_pre j dl_2 pl_2 )) (PreH12 : (P082SemanticColumns n_pre k_pre j dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticProgress n_pre k_pre j 1 dl_2 pl_2 ) ”
  &&  “ (P082ColumnProgress n_pre k_pre j 1 dl_2 pl_2 ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (j <= k_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= (k_pre + 1 ))) (PreH11 : (P082ColumnsState n_pre k_pre j dl_2 pl_2 )) (PreH12 : (P082SemanticColumns n_pre k_pre j dl_2 pl_2 )),
  (P082SemanticProgress n_pre k_pre j 1 dl_2 pl_2 )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (j <= k_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= (k_pre + 1 ))) (PreH11 : (P082ColumnsState n_pre k_pre j dl_2 pl_2 )) (PreH12 : (P082SemanticColumns n_pre k_pre j dl_2 pl_2 )),
  (P082ColumnProgress n_pre k_pre j 1 dl_2 pl_2 )
.

Definition solver_entail_wit_6 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i <= n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= k_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH14 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (j >= INT_MIN)) (PreH8 : (W >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (j >= INT_MIN)) (PreH8 : (W >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_7 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH3 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (k_pre >= INT_MIN)) (PreH6 : (i <= n_pre)) (PreH7 : (W = (k_pre + 1 ))) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= (Zmin (n_pre) (10)))) (PreH12 : (0 <= ((n_pre + 1 ) * W ))) (PreH13 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH14 : (2 <= j)) (PreH15 : (j <= k_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH19 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH2 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH13 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH14 : (k_pre <= INT_MAX)) (PreH15 : (k_pre >= INT_MIN)) (PreH16 : (i <= n_pre)) (PreH17 : (W = (k_pre + 1 ))) (PreH18 : (2 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (2 <= k_pre)) (PreH21 : (k_pre <= (Zmin (n_pre) (10)))) (PreH22 : (0 <= ((n_pre + 1 ) * W ))) (PreH23 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH24 : (2 <= j)) (PreH25 : (j <= k_pre)) (PreH26 : (1 <= i)) (PreH27 : (i <= (n_pre + 1 ))) (PreH28 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH29 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH2 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH13 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH14 : (k_pre <= INT_MAX)) (PreH15 : (k_pre >= INT_MIN)) (PreH16 : (i <= n_pre)) (PreH17 : (W = (k_pre + 1 ))) (PreH18 : (2 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (2 <= k_pre)) (PreH21 : (k_pre <= (Zmin (n_pre) (10)))) (PreH22 : (0 <= ((n_pre + 1 ) * W ))) (PreH23 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH24 : (2 <= j)) (PreH25 : (j <= k_pre)) (PreH26 : (1 <= i)) (PreH27 : (i <= (n_pre + 1 ))) (PreH28 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH29 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_8_1 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (j = k_pre)) (PreH2 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH3 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH6 : (i >= 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH2 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j = k_pre)) (PreH12 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH13 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH14 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH16 : (i >= 3)) (PreH17 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : (k_pre <= INT_MAX)) (PreH20 : (k_pre >= INT_MIN)) (PreH21 : (i <= n_pre)) (PreH22 : (W = (k_pre + 1 ))) (PreH23 : (2 <= n_pre)) (PreH24 : (n_pre <= 200000)) (PreH25 : (2 <= k_pre)) (PreH26 : (k_pre <= (Zmin (n_pre) (10)))) (PreH27 : (0 <= ((n_pre + 1 ) * W ))) (PreH28 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH29 : (2 <= j)) (PreH30 : (j <= k_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= (n_pre + 1 ))) (PreH33 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH34 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 1 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_8_1_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH2 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j = k_pre)) (PreH12 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH13 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH14 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH16 : (i >= 3)) (PreH17 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : (k_pre <= INT_MAX)) (PreH20 : (k_pre >= INT_MIN)) (PreH21 : (i <= n_pre)) (PreH22 : (W = (k_pre + 1 ))) (PreH23 : (2 <= n_pre)) (PreH24 : (n_pre <= 200000)) (PreH25 : (2 <= k_pre)) (PreH26 : (k_pre <= (Zmin (n_pre) (10)))) (PreH27 : (0 <= ((n_pre + 1 ) * W ))) (PreH28 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH29 : (2 <= j)) (PreH30 : (j <= k_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= (n_pre + 1 ))) (PreH33 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH34 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 1 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_8_2 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (j = k_pre)) (PreH2 : (i < 3)) (PreH3 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH4 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (2 <= j)) (PreH16 : (j <= k_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= (n_pre + 1 ))) (PreH19 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH20 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH2 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j = k_pre)) (PreH12 : (i < 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 1 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_8_2_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH2 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j = k_pre)) (PreH12 : (i < 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 1 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_9 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH3 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH6 : (j <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (j = k_pre)) (PreH9 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH12 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH13 : (i >= 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH2 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 2 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH2 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 2 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_10_1 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN) ”
  &&  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH2 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH10 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH11 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH12 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH13 : (i >= 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH15 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH16 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH17 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH18 : (j <= INT_MAX)) (PreH19 : (j >= INT_MIN)) (PreH20 : (j = k_pre)) (PreH21 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH22 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH23 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH24 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH25 : (i >= 3)) (PreH26 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH27 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH28 : (k_pre <= INT_MAX)) (PreH29 : (k_pre >= INT_MIN)) (PreH30 : (i <= n_pre)) (PreH31 : (W = (k_pre + 1 ))) (PreH32 : (2 <= n_pre)) (PreH33 : (n_pre <= 200000)) (PreH34 : (2 <= k_pre)) (PreH35 : (k_pre <= (Zmin (n_pre) (10)))) (PreH36 : (0 <= ((n_pre + 1 ) * W ))) (PreH37 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH38 : (2 <= j)) (PreH39 : (j <= k_pre)) (PreH40 : (1 <= i)) (PreH41 : (i <= (n_pre + 1 ))) (PreH42 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH43 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ (((i * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH2 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH10 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH11 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH12 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH13 : (i >= 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH15 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH16 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH17 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH18 : (j <= INT_MAX)) (PreH19 : (j >= INT_MIN)) (PreH20 : (j = k_pre)) (PreH21 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH22 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH23 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH24 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH25 : (i >= 3)) (PreH26 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH27 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH28 : (k_pre <= INT_MAX)) (PreH29 : (k_pre >= INT_MIN)) (PreH30 : (i <= n_pre)) (PreH31 : (W = (k_pre + 1 ))) (PreH32 : (2 <= n_pre)) (PreH33 : (n_pre <= 200000)) (PreH34 : (2 <= k_pre)) (PreH35 : (k_pre <= (Zmin (n_pre) (10)))) (PreH36 : (0 <= ((n_pre + 1 ) * W ))) (PreH37 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH38 : (2 <= j)) (PreH39 : (j <= k_pre)) (PreH40 : (1 <= i)) (PreH41 : (i <= (n_pre + 1 ))) (PreH42 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH43 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (((i * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_10_2 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH3 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH6 : (j <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (j = k_pre)) (PreH9 : (i < 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH11 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (k_pre <= INT_MAX)) (PreH13 : (k_pre >= INT_MIN)) (PreH14 : (i <= n_pre)) (PreH15 : (W = (k_pre + 1 ))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= (Zmin (n_pre) (10)))) (PreH20 : (0 <= ((n_pre + 1 ) * W ))) (PreH21 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH22 : (2 <= j)) (PreH23 : (j <= k_pre)) (PreH24 : (1 <= i)) (PreH25 : (i <= (n_pre + 1 ))) (PreH26 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH27 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH2 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (i < 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH13 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (i < 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ (((i * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH2 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (i < 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH13 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (i < 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (((i * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_10_3 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (j <> k_pre)) (PreH2 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH3 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH6 : (i >= 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH2 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j <> k_pre)) (PreH12 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH13 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH14 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH16 : (i >= 3)) (PreH17 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : (k_pre <= INT_MAX)) (PreH20 : (k_pre >= INT_MIN)) (PreH21 : (i <= n_pre)) (PreH22 : (W = (k_pre + 1 ))) (PreH23 : (2 <= n_pre)) (PreH24 : (n_pre <= 200000)) (PreH25 : (2 <= k_pre)) (PreH26 : (k_pre <= (Zmin (n_pre) (10)))) (PreH27 : (0 <= ((n_pre + 1 ) * W ))) (PreH28 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH29 : (2 <= j)) (PreH30 : (j <= k_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= (n_pre + 1 ))) (PreH33 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH34 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ (((i * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_10_3_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH2 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j <> k_pre)) (PreH12 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH13 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH14 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH16 : (i >= 3)) (PreH17 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : (k_pre <= INT_MAX)) (PreH20 : (k_pre >= INT_MIN)) (PreH21 : (i <= n_pre)) (PreH22 : (W = (k_pre + 1 ))) (PreH23 : (2 <= n_pre)) (PreH24 : (n_pre <= 200000)) (PreH25 : (2 <= k_pre)) (PreH26 : (k_pre <= (Zmin (n_pre) (10)))) (PreH27 : (0 <= ((n_pre + 1 ) * W ))) (PreH28 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH29 : (2 <= j)) (PreH30 : (j <= k_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= (n_pre + 1 ))) (PreH33 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH34 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (((i * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_10_4 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (j <> k_pre)) (PreH2 : (i < 3)) (PreH3 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH4 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (2 <= j)) (PreH16 : (j <= k_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= (n_pre + 1 ))) (PreH19 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH20 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH2 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j <> k_pre)) (PreH12 : (i < 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ (((i * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_10_4_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH2 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (W <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (j <> k_pre)) (PreH12 : (i < 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (((i * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_11_1 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN) ”
  &&  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
.

Definition solver_entail_wit_11_2 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
.

Definition solver_entail_wit_11_3 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (0 <= ((i * W ) + j ))) (PreH10 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH11 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH13 : (j <> k_pre)) (PreH14 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH17 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH18 : (i >= 3)) (PreH19 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : (k_pre <= INT_MAX)) (PreH22 : (k_pre >= INT_MIN)) (PreH23 : (i <= n_pre)) (PreH24 : (W = (k_pre + 1 ))) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre <= 200000)) (PreH27 : (2 <= k_pre)) (PreH28 : (k_pre <= (Zmin (n_pre) (10)))) (PreH29 : (0 <= ((n_pre + 1 ) * W ))) (PreH30 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH31 : (2 <= j)) (PreH32 : (j <= k_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= (n_pre + 1 ))) (PreH35 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH36 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 1 ) * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_3_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (0 <= ((i * W ) + j ))) (PreH10 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH11 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH13 : (j <> k_pre)) (PreH14 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH17 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH18 : (i >= 3)) (PreH19 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : (k_pre <= INT_MAX)) (PreH22 : (k_pre >= INT_MIN)) (PreH23 : (i <= n_pre)) (PreH24 : (W = (k_pre + 1 ))) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre <= 200000)) (PreH27 : (2 <= k_pre)) (PreH28 : (k_pre <= (Zmin (n_pre) (10)))) (PreH29 : (0 <= ((n_pre + 1 ) * W ))) (PreH30 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH31 : (2 <= j)) (PreH32 : (j <= k_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= (n_pre + 1 ))) (PreH35 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH36 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 1 ) * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_11_4 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  ((( &( "val" ) )) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (0 <= ((i * W ) + j ))) (PreH10 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH12 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH13 : (j <> k_pre)) (PreH14 : (i < 3)) (PreH15 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH16 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH17 : (k_pre <= INT_MAX)) (PreH18 : (k_pre >= INT_MIN)) (PreH19 : (i <= n_pre)) (PreH20 : (W = (k_pre + 1 ))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre <= 200000)) (PreH23 : (2 <= k_pre)) (PreH24 : (k_pre <= (Zmin (n_pre) (10)))) (PreH25 : (0 <= ((n_pre + 1 ) * W ))) (PreH26 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH27 : (2 <= j)) (PreH28 : (j <= k_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= (n_pre + 1 ))) (PreH31 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH32 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  TT && emp 
|--
  “ ((((i - 1 ) * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_4_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (0 <= ((i * W ) + j ))) (PreH10 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH12 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH13 : (j <> k_pre)) (PreH14 : (i < 3)) (PreH15 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH16 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH17 : (k_pre <= INT_MAX)) (PreH18 : (k_pre >= INT_MIN)) (PreH19 : (i <= n_pre)) (PreH20 : (W = (k_pre + 1 ))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre <= 200000)) (PreH23 : (2 <= k_pre)) (PreH24 : (k_pre <= (Zmin (n_pre) (10)))) (PreH25 : (0 <= ((n_pre + 1 ) * W ))) (PreH26 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH27 : (2 <= j)) (PreH28 : (j <= k_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= (n_pre + 1 ))) (PreH31 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH32 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  ((((i - 1 ) * (k_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_12_1 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl_2 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  “ (P082ColumnProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_12_1_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082SemanticProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_1_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082ColumnProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl_2 0) ) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + k_pre ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_2 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl_2 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  “ (P082ColumnProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_12_2_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082SemanticProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_2_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl_2 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082ColumnProgress n_pre k_pre k_pre (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + k_pre ) (replace_Znth (((i * (k_pre + 1 ) ) + k_pre )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) pl_2 0) + (Znth (((i - 1 ) * (k_pre + 1 ) ) + k_pre ) pl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_3 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl_2 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  “ (P082ColumnProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_12_3_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082SemanticProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_3_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl_2 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082ColumnProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) - (Znth (((i - 2 ) * (k_pre + 1 ) ) + (j - 1 ) ) dl_2 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_4 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((Znth (((i - 1 ) * W ) + j ) pl_2 0) + (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j (i + 1 ) dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  “ (P082ColumnProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_12_4_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082SemanticProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_12_4_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl_2 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082ColumnProgress n_pre k_pre j (i + 1 ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) (replace_Znth (((i * (k_pre + 1 ) ) + j )) ((((Znth (((i - 1 ) * (k_pre + 1 ) ) + j ) pl_2 0) + (Znth ((i * (k_pre + 1 ) ) + j ) (replace_Znth (((i * (k_pre + 1 ) ) + j )) (((((Znth (((i - 1 ) * (k_pre + 1 ) ) + (j - 1 ) ) pl_2 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl_2)) 0) ) % ( 998244353 ) )) (pl_2)) )
.

Definition solver_entail_wit_13 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= k_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH14 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl_2 )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl_2 )
|--
  EX (dl: (@list Z)) (pl: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre (j + 1 ) dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre (j + 1 ) dl pl ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= k_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH14 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  TT && emp 
|--
  “ (P082SemanticColumns n_pre k_pre (j + 1 ) dl_2 pl_2 ) ”
  &&  “ (P082ColumnsState n_pre k_pre (j + 1 ) dl_2 pl_2 ) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= k_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH14 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082SemanticColumns n_pre k_pre (j + 1 ) dl_2 pl_2 )
.

Definition solver_entail_wit_13_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl_2: (@list Z)) (pl_2: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (i > n_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= k_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (P082ColumnProgress n_pre k_pre j i dl_2 pl_2 )) (PreH14 : (P082SemanticProgress n_pre k_pre j i dl_2 pl_2 )),
  (P082ColumnsState n_pre k_pre (j + 1 ) dl_2 pl_2 )
.

Definition solver_entail_wit_14 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (j > k_pre)) (PreH2 : (W = (k_pre + 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= (Zmin (n_pre) (10)))) (PreH7 : (0 <= ((n_pre + 1 ) * W ))) (PreH8 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH9 : (2 <= j)) (PreH10 : (j <= (k_pre + 1 ))) (PreH11 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH12 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((n_pre * W ) + k_pre )) ”
  &&  “ (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (j > k_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre j dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre j dl pl ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (W <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W >= INT_MIN)) (PreH5 : (k_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j > k_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (2 <= j)) (PreH16 : (j <= (k_pre + 1 ))) (PreH17 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH18 : (P082SemanticColumns n_pre k_pre j dl pl )),
  TT && emp 
|--
  “ (((n_pre * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_14_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (W <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (W >= INT_MIN)) (PreH5 : (k_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j > k_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (2 <= j)) (PreH16 : (j <= (k_pre + 1 ))) (PreH17 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH18 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (((n_pre * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_15 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (n_pre >= 2)) (PreH2 : (0 <= ((n_pre * W ) + k_pre ))) (PreH3 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH4 : (j > k_pre)) (PreH5 : (W = (k_pre + 1 ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= k_pre)) (PreH9 : (k_pre <= (Zmin (n_pre) (10)))) (PreH10 : (0 <= ((n_pre + 1 ) * W ))) (PreH11 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH12 : (2 <= j)) (PreH13 : (j <= (k_pre + 1 ))) (PreH14 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH15 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) )) ”
  &&  “ ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((n_pre - 2 ) * W ) + k_pre )) ”
  &&  “ ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX) ”
  &&  “ ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN) ”
  &&  “ (n_pre >= 2) ”
  &&  “ (0 <= ((n_pre * W ) + k_pre )) ”
  &&  “ (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (j > k_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre j dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre j dl pl ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  ((( &( "ans" ) )) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH2 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (n_pre >= 2)) (PreH10 : (0 <= ((n_pre * W ) + k_pre ))) (PreH11 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (j > k_pre)) (PreH13 : (W = (k_pre + 1 ))) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= k_pre)) (PreH17 : (k_pre <= (Zmin (n_pre) (10)))) (PreH18 : (0 <= ((n_pre + 1 ) * W ))) (PreH19 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH20 : (2 <= j)) (PreH21 : (j <= (k_pre + 1 ))) (PreH22 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH23 : (P082SemanticColumns n_pre k_pre j dl pl )),
  TT && emp 
|--
  “ ((((n_pre - 2 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  “ ((((n_pre - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * (k_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH2 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (n_pre >= 2)) (PreH10 : (0 <= ((n_pre * W ) + k_pre ))) (PreH11 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (j > k_pre)) (PreH13 : (W = (k_pre + 1 ))) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= k_pre)) (PreH17 : (k_pre <= (Zmin (n_pre) (10)))) (PreH18 : (0 <= ((n_pre + 1 ) * W ))) (PreH19 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH20 : (2 <= j)) (PreH21 : (j <= (k_pre + 1 ))) (PreH22 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH23 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((((n_pre - 2 ) * (k_pre + 1 ) ) + k_pre ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_15_split_goal_2 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH2 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (W <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (n_pre >= 2)) (PreH10 : (0 <= ((n_pre * W ) + k_pre ))) (PreH11 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (j > k_pre)) (PreH13 : (W = (k_pre + 1 ))) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= k_pre)) (PreH17 : (k_pre <= (Zmin (n_pre) (10)))) (PreH18 : (0 <= ((n_pre + 1 ) * W ))) (PreH19 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH20 : (2 <= j)) (PreH21 : (j <= (k_pre + 1 ))) (PreH22 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH23 : (P082SemanticColumns n_pre k_pre j dl pl )),
  ((((n_pre - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * (k_pre + 1 ) ))
.

Definition solver_entail_wit_16 :=
(
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl_2 )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl_2 )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl_2 )
|--
  EX (pl: (@list Z)) (dl_2: (@list Z)),
  “ (W = (k_pre + 1 )) ”
  &&  “ (P082FinalValue n_pre k_pre dl_2 ((((Znth ((n_pre * W ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * W ) dl_2 )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl_2 )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl_2 )),
  TT && emp 
|--
  “ (P082FinalValue n_pre k_pre dl ((((Znth ((n_pre * (k_pre + 1 ) ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * (k_pre + 1 ) ) + k_pre ) dl 0) ) % ( 998244353 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_16_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl_2: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl_2 )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl_2 )),
  (P082FinalValue n_pre k_pre dl ((((Znth ((n_pre * (k_pre + 1 ) ) + k_pre ) dl 0) + (Znth (((n_pre - 2 ) * (k_pre + 1 ) ) + (k_pre - 1 ) ) dl 0) ) + (Znth (((n_pre - 2 ) * (k_pre + 1 ) ) + k_pre ) dl 0) ) % ( 998244353 ) ) )
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (W: Z) (ans: Z) (PreH1 : (W = (k_pre + 1 ))) (PreH2 : (P082FinalValue n_pre k_pre dl ans )),
  TT && emp 
|--
  “ (Spec n_pre k_pre ans ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (W: Z) (ans: Z) (PreH1 : (W = (k_pre + 1 ))) (PreH2 : (P082FinalValue n_pre k_pre dl ans )),
  TT && emp 
|--
  “ (Spec n_pre k_pre ans ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (W: Z) (ans: Z) (PreH1 : (W = (k_pre + 1 ))) (PreH2 : (P082FinalValue n_pre k_pre dl ans )),
  (Spec n_pre k_pre ans )
.

Definition solver_partial_solve_wit_1_pure :=
(
forall (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "pref" ) )) # Ptr  |->_)
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "dp" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (sizeof(INT64) = sizeof(INT64)) ”
  &&  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (k_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((k_pre + 1 ) <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((k_pre + 1 ) >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "pref" ) )) # Ptr  |->_)
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "dp" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (k_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((k_pre + 1 ) <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((k_pre + 1 ) >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "pref" ) )) # Ptr  |->_)
  **  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
  **  ((( &( "dp" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (n_pre: Z) (k_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= (Zmin (n_pre) (10)))),
  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
|--
  “ (sizeof(INT64) = sizeof(INT64)) ”
  &&  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
  &&  “ (retval <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  (Int64Array.full retval (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)) (repeat_Z (0) ((unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32)))) )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
(
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "dp" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (sizeof(INT64) = sizeof(INT64)) ”
  &&  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
) \/
(
forall (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((k_pre + 1 ) <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((k_pre + 1 ) >= INT_MIN)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "dp" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (k_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((k_pre + 1 ) <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((k_pre + 1 ) >= INT_MIN)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))),
  ((( &( "dp" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (n_pre: Z) (k_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= (Zmin (n_pre) (10)))),
  TT && emp 
|--
  “ (sizeof(INT64) = sizeof(INT64)) ”
  &&  “ (0 <= (unsigned_last_nbits (((n_pre + 1 ) * (k_pre + 1 ) )) (32))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  emp
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((i * W ) + 1 )) ”
  &&  “ (((i * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((i - 1 ) * W ) + 1 )) ”
  &&  “ ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre i dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre i dl pl ) ”
  &&  (((dp + (((i * W ) + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i dp ((i * W ) + 1 ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_4 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((i * W ) + 1 )) ”
  &&  “ (((i * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((i - 1 ) * W ) + 1 )) ”
  &&  “ ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre i dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + 1 ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + 1 ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
.

Definition solver_partial_solve_wit_5 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + 1 ))) (PreH2 : (((i * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((i - 1 ) * W ) + 1 ))) (PreH4 : ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W ))) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (k_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (W = (k_pre + 1 ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= k_pre)) (PreH12 : (k_pre <= (Zmin (n_pre) (10)))) (PreH13 : (0 <= ((n_pre + 1 ) * W ))) (PreH14 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082InitState n_pre k_pre i dl pl )) (PreH18 : (P082SemanticInit n_pre k_pre i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
|--
  “ (0 <= ((i * W ) + 1 )) ”
  &&  “ (((i * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((i - 1 ) * W ) + 1 )) ”
  &&  “ ((((i - 1 ) * W ) + 1 ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082InitState n_pre k_pre i dl pl ) ”
  &&  “ (P082SemanticInit n_pre k_pre i dl pl ) ”
  &&  (((pref + (((i * W ) + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pref ((i * W ) + 1 ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + 1 )) (1) (dl)) )
.

Definition solver_partial_solve_wit_6 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (W = (k_pre + 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= (Zmin (n_pre) (10)))) (PreH11 : (0 <= ((n_pre + 1 ) * W ))) (PreH12 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH13 : (2 <= j)) (PreH14 : (j <= k_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH18 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + (j - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + (j - 1 ) ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_7 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH2 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (i <= n_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= k_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= (n_pre + 1 ))) (PreH22 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH23 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + ((((i - 2 ) * W ) + (j - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0))
  **  (Int64Array.missing_i dp (((i - 2 ) * W ) + (j - 1 ) ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_8 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + k_pre ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + k_pre ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + k_pre ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_9 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH2 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (j = k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + k_pre ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + k_pre ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + k_pre ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_10 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH2 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i >= 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH9 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH16 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH17 : (i >= 3)) (PreH18 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH19 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH20 : (k_pre <= INT_MAX)) (PreH21 : (k_pre >= INT_MIN)) (PreH22 : (i <= n_pre)) (PreH23 : (W = (k_pre + 1 ))) (PreH24 : (2 <= n_pre)) (PreH25 : (n_pre <= 200000)) (PreH26 : (2 <= k_pre)) (PreH27 : (k_pre <= (Zmin (n_pre) (10)))) (PreH28 : (0 <= ((n_pre + 1 ) * W ))) (PreH29 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH30 : (2 <= j)) (PreH31 : (j <= k_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= (n_pre + 1 ))) (PreH34 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH35 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + ((((i - 2 ) * W ) + k_pre ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 2 ) * W ) + k_pre ) dl 0))
  **  (Int64Array.missing_i dp (((i - 2 ) * W ) + k_pre ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_11 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH4 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH5 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH6 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH7 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH8 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH9 : (i >= 3)) (PreH10 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH11 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH12 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH13 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH14 : (j <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (j = k_pre)) (PreH17 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH18 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH19 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH20 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH21 : (i >= 3)) (PreH22 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH23 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH24 : (k_pre <= INT_MAX)) (PreH25 : (k_pre >= INT_MIN)) (PreH26 : (i <= n_pre)) (PreH27 : (W = (k_pre + 1 ))) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre <= 200000)) (PreH30 : (2 <= k_pre)) (PreH31 : (k_pre <= (Zmin (n_pre) (10)))) (PreH32 : (0 <= ((n_pre + 1 ) * W ))) (PreH33 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH34 : (2 <= j)) (PreH35 : (j <= k_pre)) (PreH36 : (1 <= i)) (PreH37 : (i <= (n_pre + 1 ))) (PreH38 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH39 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN) ”
  &&  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_12 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH5 : (i < 3)) (PreH6 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH7 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (j >= INT_MIN)) (PreH12 : (j = k_pre)) (PreH13 : (i < 3)) (PreH14 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH15 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH16 : (k_pre <= INT_MAX)) (PreH17 : (k_pre >= INT_MIN)) (PreH18 : (i <= n_pre)) (PreH19 : (W = (k_pre + 1 ))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (2 <= k_pre)) (PreH23 : (k_pre <= (Zmin (n_pre) (10)))) (PreH24 : (0 <= ((n_pre + 1 ) * W ))) (PreH25 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH26 : (2 <= j)) (PreH27 : (j <= k_pre)) (PreH28 : (1 <= i)) (PreH29 : (i <= (n_pre + 1 ))) (PreH30 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH31 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_13 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH4 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH7 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH9 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH10 : (i >= 3)) (PreH11 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH12 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH13 : (k_pre <= INT_MAX)) (PreH14 : (k_pre >= INT_MIN)) (PreH15 : (i <= n_pre)) (PreH16 : (W = (k_pre + 1 ))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= (Zmin (n_pre) (10)))) (PreH21 : (0 <= ((n_pre + 1 ) * W ))) (PreH22 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH23 : (2 <= j)) (PreH24 : (j <= k_pre)) (PreH25 : (1 <= i)) (PreH26 : (i <= (n_pre + 1 ))) (PreH27 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH28 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_14 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= ((i * W ) + j ))) (PreH2 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH4 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH5 : (j <> k_pre)) (PreH6 : (i < 3)) (PreH7 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH8 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (k_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (i <= n_pre)) (PreH12 : (W = (k_pre + 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= (Zmin (n_pre) (10)))) (PreH17 : (0 <= ((n_pre + 1 ) * W ))) (PreH18 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH19 : (2 <= j)) (PreH20 : (j <= k_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= (n_pre + 1 ))) (PreH23 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH24 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_15 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN) ”
  &&  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + j ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_16 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN) ”
  &&  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0))
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_17 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX)) (PreH6 : (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN)) (PreH7 : (0 <= (((i - 2 ) * W ) + k_pre ))) (PreH8 : ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH9 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH10 : ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH11 : (i >= 3)) (PreH12 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH13 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH14 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH15 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (j >= INT_MIN)) (PreH18 : (j = k_pre)) (PreH19 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH20 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH21 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH22 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH23 : (i >= 3)) (PreH24 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH25 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH26 : (k_pre <= INT_MAX)) (PreH27 : (k_pre >= INT_MIN)) (PreH28 : (i <= n_pre)) (PreH29 : (W = (k_pre + 1 ))) (PreH30 : (2 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (2 <= k_pre)) (PreH33 : (k_pre <= (Zmin (n_pre) (10)))) (PreH34 : (0 <= ((n_pre + 1 ) * W ))) (PreH35 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH36 : (2 <= j)) (PreH37 : (j <= k_pre)) (PreH38 : (1 <= i)) (PreH39 : (i <= (n_pre + 1 ))) (PreH40 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH41 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) >= INT64_MIN) ”
  &&  “ (0 <= (((i - 2 ) * W ) + k_pre )) ”
  &&  “ ((((i - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ ((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pref ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) - (Znth (((i - 2 ) * W ) + k_pre ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_18 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + j ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_19 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0))
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_20 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN)) (PreH7 : (i < 3)) (PreH8 : (0 <= (((i - 1 ) * W ) + k_pre ))) (PreH9 : ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (j <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (j = k_pre)) (PreH15 : (i < 3)) (PreH16 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH17 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH18 : (k_pre <= INT_MAX)) (PreH19 : (k_pre >= INT_MIN)) (PreH20 : (i <= n_pre)) (PreH21 : (W = (k_pre + 1 ))) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre <= 200000)) (PreH24 : (2 <= k_pre)) (PreH25 : (k_pre <= (Zmin (n_pre) (10)))) (PreH26 : (0 <= ((n_pre + 1 ) * W ))) (PreH27 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH28 : (2 <= j)) (PreH29 : (j <= k_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= (n_pre + 1 ))) (PreH32 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH33 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) >= INT64_MIN) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + k_pre )) ”
  &&  “ ((((i - 1 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (j = k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pref ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) + (Znth (((i - 1 ) * W ) + k_pre ) pl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_21 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + j ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_22 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0))
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_23 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX)) (PreH6 : (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (0 <= (((i - 2 ) * W ) + (j - 1 ) ))) (PreH9 : ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH11 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH12 : (i >= 3)) (PreH13 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH14 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH15 : (k_pre <= INT_MAX)) (PreH16 : (k_pre >= INT_MIN)) (PreH17 : (i <= n_pre)) (PreH18 : (W = (k_pre + 1 ))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= (Zmin (n_pre) (10)))) (PreH23 : (0 <= ((n_pre + 1 ) * W ))) (PreH24 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH25 : (2 <= j)) (PreH26 : (j <= k_pre)) (PreH27 : (1 <= i)) (PreH28 : (i <= (n_pre + 1 ))) (PreH29 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH30 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) <= INT64_MAX) ”
  &&  “ (((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (0 <= (((i - 2 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 2 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (i >= 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pref ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) ((((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) - (Znth (((i - 2 ) * W ) + (j - 1 ) ) dl 0) ) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_24 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + ((((i - 1 ) * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - 1 ) * W ) + j ) pl 0))
  **  (Int64Array.missing_i pref (((i - 1 ) * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_25 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((dp + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |-> (Znth ((i * W ) + j ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) 0))
  **  (Int64Array.missing_i dp ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_26 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (i: Z) (j: Z) (W: Z) (PreH1 : (0 <= (((i - 1 ) * W ) + j ))) (PreH2 : ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= ((i * W ) + j ))) (PreH4 : (((i * W ) + j ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX)) (PreH6 : ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN)) (PreH7 : (j <> k_pre)) (PreH8 : (i < 3)) (PreH9 : (0 <= (((i - 1 ) * W ) + (j - 1 ) ))) (PreH10 : ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (k_pre <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (i <= n_pre)) (PreH14 : (W = (k_pre + 1 ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= k_pre)) (PreH18 : (k_pre <= (Zmin (n_pre) (10)))) (PreH19 : (0 <= ((n_pre + 1 ) * W ))) (PreH20 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH21 : (2 <= j)) (PreH22 : (j <= k_pre)) (PreH23 : (1 <= i)) (PreH24 : (i <= (n_pre + 1 ))) (PreH25 : (P082ColumnProgress n_pre k_pre j i dl pl )) (PreH26 : (P082SemanticProgress n_pre k_pre j i dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((i - 1 ) * W ) + j )) ”
  &&  “ ((((i - 1 ) * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= ((i * W ) + j )) ”
  &&  “ (((i * W ) + j ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) <= INT64_MAX) ”
  &&  “ ((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) >= INT64_MIN) ”
  &&  “ (j <> k_pre) ”
  &&  “ (i < 3) ”
  &&  “ (0 <= (((i - 1 ) * W ) + (j - 1 ) )) ”
  &&  “ ((((i - 1 ) * W ) + (j - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (k_pre <= INT_MAX) ”
  &&  “ (k_pre >= INT_MIN) ”
  &&  “ (i <= n_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= k_pre) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre + 1 )) ”
  &&  “ (P082ColumnProgress n_pre k_pre j i dl pl ) ”
  &&  “ (P082SemanticProgress n_pre k_pre j i dl pl ) ”
  &&  (((pref + (((i * W ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pref ((i * W ) + j ) 0 ((n_pre + 1 ) * W ) pl )
  **  (Int64Array.full dp ((n_pre + 1 ) * W ) (replace_Znth (((i * W ) + j )) (((((Znth (((i - 1 ) * W ) + (j - 1 ) ) pl 0) % ( 998244353 ) ) + 998244353 ) % ( 998244353 ) )) (dl)) )
.

Definition solver_partial_solve_wit_27 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= ((n_pre * W ) + k_pre ))) (PreH2 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (j > k_pre)) (PreH4 : (W = (k_pre + 1 ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= k_pre)) (PreH8 : (k_pre <= (Zmin (n_pre) (10)))) (PreH9 : (0 <= ((n_pre + 1 ) * W ))) (PreH10 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH11 : (2 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH14 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= ((n_pre * W ) + k_pre )) ”
  &&  “ (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (j > k_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre j dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre j dl pl ) ”
  &&  (((dp + (((n_pre * W ) + k_pre ) * sizeof(INT64)))) # Int64  |-> (Znth ((n_pre * W ) + k_pre ) dl 0))
  **  (Int64Array.missing_i dp ((n_pre * W ) + k_pre ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_28 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) )) ”
  &&  “ ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((n_pre - 2 ) * W ) + k_pre )) ”
  &&  “ ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX) ”
  &&  “ ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN) ”
  &&  “ (n_pre >= 2) ”
  &&  “ (0 <= ((n_pre * W ) + k_pre )) ”
  &&  “ (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (j > k_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre j dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre j dl pl ) ”
  &&  (((dp + ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) dl 0))
  **  (Int64Array.missing_i dp (((n_pre - 2 ) * W ) + (k_pre - 1 ) ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_29 :=
forall (n_pre: Z) (k_pre: Z) (pref: Z) (dp: Z) (dl: (@list Z)) (pl: (@list Z)) (j: Z) (W: Z) (PreH1 : (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) ))) (PreH2 : ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH3 : (0 <= (((n_pre - 2 ) * W ) + k_pre ))) (PreH4 : ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH5 : ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX)) (PreH6 : ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN)) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= ((n_pre * W ) + k_pre ))) (PreH9 : (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W ))) (PreH10 : (j > k_pre)) (PreH11 : (W = (k_pre + 1 ))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (2 <= k_pre)) (PreH15 : (k_pre <= (Zmin (n_pre) (10)))) (PreH16 : (0 <= ((n_pre + 1 ) * W ))) (PreH17 : (((n_pre + 1 ) * W ) <= UINT_MAX)) (PreH18 : (2 <= j)) (PreH19 : (j <= (k_pre + 1 ))) (PreH20 : (P082ColumnsState n_pre k_pre j dl pl )) (PreH21 : (P082SemanticColumns n_pre k_pre j dl pl )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (0 <= (((n_pre - 2 ) * W ) + (k_pre - 1 ) )) ”
  &&  “ ((((n_pre - 2 ) * W ) + (k_pre - 1 ) ) < ((n_pre + 1 ) * W )) ”
  &&  “ (0 <= (((n_pre - 2 ) * W ) + k_pre )) ”
  &&  “ ((((n_pre - 2 ) * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ ((Znth ((n_pre * W ) + k_pre ) dl 0) <= INT64_MAX) ”
  &&  “ ((Znth ((n_pre * W ) + k_pre ) dl 0) >= INT64_MIN) ”
  &&  “ (n_pre >= 2) ”
  &&  “ (0 <= ((n_pre * W ) + k_pre )) ”
  &&  “ (((n_pre * W ) + k_pre ) < ((n_pre + 1 ) * W )) ”
  &&  “ (j > k_pre) ”
  &&  “ (W = (k_pre + 1 )) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (2 <= k_pre) ”
  &&  “ (k_pre <= (Zmin (n_pre) (10))) ”
  &&  “ (0 <= ((n_pre + 1 ) * W )) ”
  &&  “ (((n_pre + 1 ) * W ) <= UINT_MAX) ”
  &&  “ (2 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ (P082ColumnsState n_pre k_pre j dl pl ) ”
  &&  “ (P082SemanticColumns n_pre k_pre j dl pl ) ”
  &&  (((dp + ((((n_pre - 2 ) * W ) + k_pre ) * sizeof(INT64)))) # Int64  |-> (Znth (((n_pre - 2 ) * W ) + k_pre ) dl 0))
  **  (Int64Array.missing_i dp (((n_pre - 2 ) * W ) + k_pre ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_30 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (W: Z) (ans: Z) (dp: Z) (pref: Z) (PreH1 : (W = (k_pre + 1 ))) (PreH2 : (P082FinalValue n_pre k_pre dl ans )),
  (Int64Array.full dp ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (W = (k_pre + 1 )) ”
  &&  “ (P082FinalValue n_pre k_pre dl ans ) ”
  &&  (Int64Array.full dp ((n_pre + 1 ) * (k_pre + 1 ) ) dl )
  **  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
.

Definition solver_partial_solve_wit_31 :=
forall (n_pre: Z) (k_pre: Z) (dl: (@list Z)) (pl: (@list Z)) (W: Z) (ans: Z) (pref: Z) (PreH1 : (W = (k_pre + 1 ))) (PreH2 : (P082FinalValue n_pre k_pre dl ans )),
  (Int64Array.full pref ((n_pre + 1 ) * W ) pl )
|--
  “ (W = (k_pre + 1 )) ”
  &&  “ (P082FinalValue n_pre k_pre dl ans ) ”
  &&  (Int64Array.full pref ((n_pre + 1 ) * (k_pre + 1 ) ) pl )
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
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Axiom proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Axiom proof_of_solver_safety_wit_60 : solver_safety_wit_60.
Axiom proof_of_solver_safety_wit_61 : solver_safety_wit_61.
Axiom proof_of_solver_safety_wit_62 : solver_safety_wit_62.
Axiom proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Axiom proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Axiom proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Axiom proof_of_solver_safety_wit_66 : solver_safety_wit_66.
Axiom proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Axiom proof_of_solver_safety_wit_68 : solver_safety_wit_68.
Axiom proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Axiom proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Axiom proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Axiom proof_of_solver_safety_wit_72 : solver_safety_wit_72.
Axiom proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Axiom proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Axiom proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Axiom proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Axiom proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Axiom proof_of_solver_safety_wit_78 : solver_safety_wit_78.
Axiom proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Axiom proof_of_solver_safety_wit_80 : solver_safety_wit_80.
Axiom proof_of_solver_safety_wit_81 : solver_safety_wit_81.
Axiom proof_of_solver_safety_wit_82 : solver_safety_wit_82.
Axiom proof_of_solver_safety_wit_83 : solver_safety_wit_83.
Axiom proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Axiom proof_of_solver_safety_wit_85 : solver_safety_wit_85.
Axiom proof_of_solver_safety_wit_86 : solver_safety_wit_86.
Axiom proof_of_solver_safety_wit_87 : solver_safety_wit_87.
Axiom proof_of_solver_safety_wit_88 : solver_safety_wit_88.
Axiom proof_of_solver_safety_wit_89 : solver_safety_wit_89.
Axiom proof_of_solver_safety_wit_90 : solver_safety_wit_90.
Axiom proof_of_solver_safety_wit_91 : solver_safety_wit_91.
Axiom proof_of_solver_safety_wit_92 : solver_safety_wit_92.
Axiom proof_of_solver_safety_wit_93 : solver_safety_wit_93.
Axiom proof_of_solver_safety_wit_94 : solver_safety_wit_94.
Axiom proof_of_solver_safety_wit_95 : solver_safety_wit_95.
Axiom proof_of_solver_safety_wit_96 : solver_safety_wit_96.
Axiom proof_of_solver_safety_wit_97 : solver_safety_wit_97.
Axiom proof_of_solver_safety_wit_98 : solver_safety_wit_98.
Axiom proof_of_solver_safety_wit_99 : solver_safety_wit_99.
Axiom proof_of_solver_safety_wit_100 : solver_safety_wit_100.
Axiom proof_of_solver_safety_wit_101 : solver_safety_wit_101.
Axiom proof_of_solver_safety_wit_102 : solver_safety_wit_102.
Axiom proof_of_solver_safety_wit_103 : solver_safety_wit_103.
Axiom proof_of_solver_safety_wit_104 : solver_safety_wit_104.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Axiom proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Axiom proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Axiom proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.

End VC_Correct.
