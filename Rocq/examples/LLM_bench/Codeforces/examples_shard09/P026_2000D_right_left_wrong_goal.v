From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P026_2000D_right_left_wrong_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)),
  ((( &( "i" ) )) # Int  |->_)
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (((Znth (i - 0 ) prefix 0) + (Znth i values 0) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre directions )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) prefix 0) + (Znth i values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) prefix 0) + (Znth i values 0) )) ”
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) prefix 0) + (Znth i values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) prefix 0) + (Znth i values 0) )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) prefix 0) + (Znth i values 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) prefix 0) + (Znth i values 0) )) ”
.

Definition solver_safety_wit_8 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix )),
  ((( &( "score" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix )),
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "l" ) )) # Int  |-> 0)
  **  ((( &( "score" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix )),
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "l" ) )) # Int  |-> 0)
  **  ((( &( "score" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix )),
  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "score" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (76 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 76) ”
.

Definition solver_safety_wit_13 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : ((Znth l directions 0) <> 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((l + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (l + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (82 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 82) ”
.

Definition solver_safety_wit_15 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : ((Znth r directions 0) <> 82)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((r - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : (l >= r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ False ”
.

Definition solver_safety_wit_17 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l >= r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ False ”
.

Definition solver_safety_wit_18 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) )) ”
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) )) ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((INT64_MIN) <= (score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) )) ”
.

Definition solver_safety_wit_19 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) )) ”
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((INT64_MIN) <= ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) )) ”
.

Definition solver_safety_wit_20 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> score)
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> (score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((l + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (l + 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "l" ) )) # Int  |-> (l + 1 ))
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "score" ) )) # Int64  |-> (score + ((Znth (r + 1 ) prefix 0) - (Znth l prefix 0) ) ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)),
  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (0 + 1 )) ”
  &&  “ (PrefixSumsPrefix values prefix ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.seg pre_pre 0 (0 + 1 ) prefix )
  **  (Int64Array.undef_seg pre_pre (0 + 1 ) (n_pre + 1 ) )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)),
  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (0 + 1 )) ”
  &&  “ (PrefixSumsPrefix values prefix ) ”
  &&  (Int64Array.seg pre_pre 0 (0 + 1 ) prefix )
).

Definition solver_entail_wit_2 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix_2) ((cons (((Znth (i - 0 ) prefix_2 0) + (Znth i values 0) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (prefix)) = ((i + 1 ) + 1 )) ”
  &&  “ (PrefixSumsPrefix values prefix ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) prefix )
  **  (Int64Array.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  TT && emp 
|--
  “ (PrefixSumsPrefix values (app (prefix_2) ((cons (((Znth (i - 0 ) prefix_2 0) + (Znth i values 0) )) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app (prefix_2) ((cons (((Znth (i - 0 ) prefix_2 0) + (Znth i values 0) )) ((@nil Z))))))) = ((i + 1 ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  (PrefixSumsPrefix values (app (prefix_2) ((cons (((Znth (i - 0 ) prefix_2 0) + (Znth i values 0) )) ((@nil Z))))) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  ((Zlength ((app (prefix_2) ((cons (((Znth (i - 0 ) prefix_2 0) + (Znth i values 0) )) ((@nil Z))))))) = ((i + 1 ) + 1 ))
.

Definition solver_entail_wit_3 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix_2 )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  TT && emp 
|--
  “ (PrefixSums values prefix_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  (PrefixSums values prefix_2 )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix_2 )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_entail_wit_4 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH4 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix_2 )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < n_pre) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ (0 <= ((n_pre - 1 ) + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions 0 (n_pre - 1 ) 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH4 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix_2 )),
  TT && emp 
|--
  “ (GreedyProgress values directions 0 (n_pre - 1 ) 0 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH4 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix_2 )),
  (GreedyProgress values directions 0 (n_pre - 1 ) 0 )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH4 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (prefix_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH4 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)) (PreH7 : (PrefixSums values prefix_2 )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_entail_wit_5 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_entail_wit_6 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) <> 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= (l + 1 )) ”
  &&  “ ((l + 1 ) < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ ((l + 1 ) <= r) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions (l + 1 ) r score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) <> 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ (GreedyProgress values directions (l + 1 ) r score ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) <> 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  (GreedyProgress values directions (l + 1 ) r score )
.

Definition solver_entail_wit_7_1 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ ((l < r) -> ((Znth l directions 0) = 76)) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_7_1_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix_2 )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_entail_wit_7_2 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) = 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ ((l < r) -> ((Znth l directions 0) = 76)) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) = 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) = 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_7_2_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth l directions 0) = 76)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_entail_wit_8 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth r directions 0) <> 82)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= (r - 1 )) ”
  &&  “ ((r - 1 ) < n_pre) ”
  &&  “ (l <= (r - 1 )) ”
  &&  “ ((l < (r - 1 )) -> ((Znth l directions 0) = 76)) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l (r - 1 ) score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth r directions 0) <> 82)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ (GreedyProgress values directions l (r - 1 ) score ) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : ((Znth r directions 0) <> 82)) (PreH2 : (l < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  (GreedyProgress values directions l (r - 1 ) score )
.

Definition solver_entail_wit_9_1 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
  **  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= (l + 1 )) ”
  &&  “ ((l + 1 ) < n_pre) ”
  &&  “ (0 <= (r - 1 )) ”
  &&  “ ((r - 1 ) < n_pre) ”
  &&  “ ((l + 1 ) <= ((r - 1 ) + 1 )) ”
  &&  “ (0 <= (score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) )) ”
  &&  “ ((score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ) <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions (l + 1 ) (r - 1 ) (score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ (GreedyProgress values directions (l + 1 ) (r - 1 ) (score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ) ) ”
  &&  “ ((score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ) <= 2000000000000000) ”
  &&  “ (0 <= (score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_9_1_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (GreedyProgress values directions (l + 1 ) (r - 1 ) (score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ) )
.

Definition solver_entail_wit_9_1_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  ((score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ) <= 2000000000000000)
.

Definition solver_entail_wit_9_1_split_goal_3 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (0 <= (score + ((Znth (r + 1 ) prefix_2 0) - (Znth l prefix_2 0) ) ))
.

Definition solver_entail_wit_9_1_split_goal_4 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_9_1_split_goal_5 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix_2 )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_entail_wit_9_2 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (l >= r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= (r + 1 )) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (l >= r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_9_2_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (l >= r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))
.

Definition solver_entail_wit_9_2_split_goal_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (score: Z) (r: Z) (l: Z) (prefix_2: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (l >= r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 100000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> (((Znth k_4 directions 0) = 76) \/ ((Znth k_4 directions 0) = 82)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (directions)) = n_pre)) (PreH9 : (PrefixSums values prefix_2 )) (PreH10 : (0 <= l)) (PreH11 : (l < n_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < n_pre)) (PreH14 : (l <= r)) (PreH15 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH16 : (0 <= score)) (PreH17 : (score <= 2000000000000000)) (PreH18 : (GreedyProgress values directions l r score )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))
.

Definition solver_return_wit_1 :=
(
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (Spec values directions score ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
) \/
(
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (Spec values directions score ) ”
  &&  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
).

Definition solver_return_wit_1_split_goal_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (Spec values directions score ) ”
.

Definition solver_return_wit_1_split_goal_spatial :=
forall (directions: (@list Z)) (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= (r + 1 ))) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_1 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (directions)) = n_pre)),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100000))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 directions 0) = 76) \/ ((Znth i_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
.

Definition solver_partial_solve_wit_2 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix values prefix ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) prefix 0))
  **  (Int64Array.missing_i pre_pre i 0 (i + 1 ) prefix )
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_3 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix values prefix ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_4 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (prefix)) = (i + 1 ))) (PreH11 : (PrefixSumsPrefix values prefix )),
  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix values prefix ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
.

Definition solver_partial_solve_wit_5 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : (0 <= score)) (PreH15 : (score <= 2000000000000000)) (PreH16 : (GreedyProgress values directions l r score )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (l < r) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (((s_pre + (l * sizeof(CHAR)))) # Char  |-> (Znth l directions 0))
  **  (CharArray.missing_i s_pre l 0 n_pre directions )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
.

Definition solver_partial_solve_wit_6 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (directions)) = n_pre)) (PreH8 : (PrefixSums values prefix )) (PreH9 : (0 <= l)) (PreH10 : (l < n_pre)) (PreH11 : (0 <= r)) (PreH12 : (r < n_pre)) (PreH13 : (l <= r)) (PreH14 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH15 : (0 <= score)) (PreH16 : (score <= 2000000000000000)) (PreH17 : (GreedyProgress values directions l r score )),
  (IntArray.full a_pre n_pre values )
  **  (CharArray.full s_pre n_pre directions )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (l < r) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ ((l < r) -> ((Znth l directions 0) = 76)) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (((s_pre + (r * sizeof(CHAR)))) # Char  |-> (Znth r directions 0))
  **  (CharArray.missing_i s_pre r 0 n_pre directions )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
.

Definition solver_partial_solve_wit_7 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (l < r) ”
  &&  “ ((Znth r directions 0) = 82) ”
  &&  “ (l < r) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ ((l < r) -> ((Znth l directions 0) = 76)) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (((pre_pre + ((r + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (r + 1 ) prefix 0))
  **  (Int64Array.missing_i pre_pre (r + 1 ) 0 (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_8 :=
forall (directions: (@list Z)) (values: (@list Z)) (a_pre: Z) (s_pre: Z) (n_pre: Z) (pre_pre: Z) (score: Z) (r: Z) (l: Z) (prefix: (@list Z)) (PreH1 : (l < r)) (PreH2 : ((Znth r directions 0) = 82)) (PreH3 : (l < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Zlength (directions)) = n_pre)) (PreH10 : (PrefixSums values prefix )) (PreH11 : (0 <= l)) (PreH12 : (l < n_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < n_pre)) (PreH15 : (l <= r)) (PreH16 : ((l < r) -> ((Znth l directions 0) = 76))) (PreH17 : (0 <= score)) (PreH18 : (score <= 2000000000000000)) (PreH19 : (GreedyProgress values directions l r score )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (l < r) ”
  &&  “ ((Znth r directions 0) = 82) ”
  &&  “ (l < r) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 directions 0) = 76) \/ ((Znth k_2 directions 0) = 82))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (directions)) = n_pre) ”
  &&  “ (PrefixSums values prefix ) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < n_pre) ”
  &&  “ (l <= r) ”
  &&  “ ((l < r) -> ((Znth l directions 0) = 76)) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= 2000000000000000) ”
  &&  “ (GreedyProgress values directions l r score ) ”
  &&  (((pre_pre + (l * sizeof(INT64)))) # Int64  |-> (Znth l prefix 0))
  **  (Int64Array.missing_i pre_pre l 0 (n_pre + 1 ) prefix )
  **  (CharArray.full s_pre n_pre directions )
  **  (IntArray.full a_pre n_pre values )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.

End VC_Correct.
