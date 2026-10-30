From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i source 0)) /\ ((Znth i source 0) <= 122)))) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target 0)) /\ ((Znth i_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "cnt" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (((Znth i source 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i source 0) - 97 )) ”
.

Definition solver_safety_wit_3 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_4 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) ”
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) ”
).

Definition solver_safety_wit_4_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ ((INT_MIN) <= ((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full t_pre n_pre target )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth i target 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i target 0) - 97 )) ”
.

Definition solver_safety_wit_6 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full t_pre n_pre target )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_7 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 )) ”
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ ((INT_MIN) <= ((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i target 0) - 97 )) (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0) + 1 )) ((replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)))) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (CountedPrefix source target n_pre counts )) (PreH11 : (CountsEvenBefore counts c )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (26 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 26) ”
.

Definition solver_safety_wit_11 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts )) (PreH12 : (CountsEvenBefore counts c )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (((Znth c counts 0) <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_12 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts )) (PreH12 : (CountsEvenBefore counts c )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_13 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts )) (PreH9 : (CombinedOddAt source target c )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_14 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts )) (PreH9 : (CombinedOddAt source target c )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts )) (PreH12 : (CountsEvenBefore counts c )) (PreH13 : (((Znth c counts 0) % ( 2 ) ) = 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ ((c + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts )) (PreH9 : (CombinedEven source target )),
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts )) (PreH9 : (CombinedEven source target )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops)))) (PreH15 : (OperationLists ops is js )) (PreH16 : (RepairState source target ss tt i ops )),
  ((( &( "j" ) )) # Int  |->_)
  **  (CharArray.full t_pre n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops)))) (PreH15 : (OperationLists ops is js )) (PreH16 : (RepairState source target ss tt i ops )),
  ((( &( "j" ) )) # Int  |->_)
  **  (CharArray.full t_pre n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : ((Znth j ss 0) <> (Znth i ss 0))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js )) (PreH20 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js )) (PreH20 : (RepairState source target ss tt i ops )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_22 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_23 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_24 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition solver_safety_wit_28 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js )) (PreH20 : (RepairState source target ss tt i ops )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js )) (PreH20 : (RepairState source target ss tt i ops )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : ((Znth j tt 0) <> (Znth i ss 0))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_31 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_32 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_33 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_34 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_35 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_38 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_39 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j ss 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((m + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_41 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_42 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_43 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_44 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oj_pre ((m + 1 ) + 1 ) (app ((app (js) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  ((( &( "tmp" ) )) # Char  |-> (Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (((m + 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((m + 1 ) + 1 )) ”
.

Definition solver_safety_wit_45 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oj_pre ((m + 1 ) + 1 ) (app ((app (js) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> ((m + 1 ) + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_46 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : ((Znth i ss 0) = (Znth i tt 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops)))) (PreH15 : (OperationLists ops is js )) (PreH16 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_47 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "oi" ) )) # Ptr  |-> oi_pre)
  **  ((( &( "oj" ) )) # Ptr  |-> oj_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i source 0)) /\ ((Znth i source 0) <= 122)))) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target 0)) /\ ((Znth i_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)),
  (IntArray.full ( &( "cnt" ) ) 26 (repeat_Z (0) (26)) )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  EX (counts: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (CountedPrefix source target 0 counts ) ”
  &&  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i source 0)) /\ ((Znth i source 0) <= 122)))) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target 0)) /\ ((Znth i_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)),
  TT && emp 
|--
  “ (CountedPrefix source target 0 (repeat_Z (0) (26)) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i source 0)) /\ ((Znth i source 0) <= 122)))) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target 0)) /\ ((Znth i_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)),
  (CountedPrefix source target 0 (repeat_Z (0) (26)) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i source 0)) /\ ((Znth i source 0) <= 122)))) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target 0)) /\ ((Znth i_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i source 0)) /\ ((Znth i source 0) <= 122)))) (PreH5 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target 0)) /\ ((Znth i_2 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_2 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i target 0) - 97 )) (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts_2 0) + 1 )) (counts_2)) 0) + 1 )) ((replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts_2 0) + 1 )) (counts_2)))) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  EX (counts: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (CountedPrefix source target (i + 1 ) counts ) ”
  &&  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  TT && emp 
|--
  “ (CountedPrefix source target (i + 1 ) (replace_Znth (((Znth i target 0) - 97 )) (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts_2 0) + 1 )) (counts_2)) 0) + 1 )) ((replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts_2 0) + 1 )) (counts_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  (CountedPrefix source target (i + 1 ) (replace_Znth (((Znth i target 0) - 97 )) (((Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts_2 0) + 1 )) (counts_2)) 0) + 1 )) ((replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts_2 0) + 1 )) (counts_2)))) )
.

Definition solver_entail_wit_3 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 26) ”
  &&  “ (CountedPrefix source target n_pre counts ) ”
  &&  “ (CountsEvenBefore counts 0 ) ”
  &&  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  TT && emp 
|--
  “ (CountsEvenBefore counts_2 0 ) ”
  &&  “ (CountedPrefix source target n_pre counts_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  (CountsEvenBefore counts_2 0 )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  (CountedPrefix source target n_pre counts_2 )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2 )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_4 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )) (PreH13 : (((Znth c counts_2 0) % ( 2 ) ) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  EX (counts: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 26) ”
  &&  “ (CountedPrefix source target n_pre counts ) ”
  &&  “ (CombinedOddAt source target c ) ”
  &&  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )) (PreH13 : (((Znth c counts_2 0) % ( 2 ) ) <> 0)),
  TT && emp 
|--
  “ (CombinedOddAt source target c ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )) (PreH13 : (((Znth c counts_2 0) % ( 2 ) ) <> 0)),
  (CombinedOddAt source target c )
.

Definition solver_entail_wit_5 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (CountedPrefix source target n_pre counts ) ”
  &&  “ (CombinedEven source target ) ”
  &&  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )),
  TT && emp 
|--
  “ (CombinedEven source target ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )),
  (CombinedEven source target )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_5_split_goal_3 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_6 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )) (PreH13 : (((Znth c counts_2 0) % ( 2 ) ) = 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  EX (counts: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 26) ”
  &&  “ (CountedPrefix source target n_pre counts ) ”
  &&  “ (CountsEvenBefore counts (c + 1 ) ) ”
  &&  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )) (PreH13 : (((Znth c counts_2 0) % ( 2 ) ) = 0)),
  TT && emp 
|--
  “ (CountsEvenBefore counts_2 (c + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2 )) (PreH12 : (CountsEvenBefore counts_2 c )) (PreH13 : (((Znth c counts_2 0) % ( 2 ) ) = 0)),
  (CountsEvenBefore counts_2 (c + 1 ) )
.

Definition solver_entail_wit_7 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts_2 )) (PreH9 : (CombinedEven source target )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (2 * 0 )) ”
  &&  “ (0 = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt 0 ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre 0 is )
  **  (IntArray.undef_seg oi_pre 0 (2 * n_pre ) )
  **  (IntArray.full oj_pre 0 js )
  **  (IntArray.undef_seg oj_pre 0 (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (counts_2: (@list Z)) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source 0)) /\ ((Znth k_3 source 0) <= 122)))) (PreH5 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target 0)) /\ ((Znth k_4 target 0) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts_2 )) (PreH9 : (CombinedEven source target )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (source))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (2 * 0 )) ”
  &&  “ (0 = (Zlength (ops))) ”
  &&  “ (OperationLists ops (@nil Z) (@nil Z) ) ”
  &&  “ (RepairState source target source target 0 ops ) ”
  &&  emp
).

Definition solver_entail_wit_8 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2 )) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (CharArray.full t_pre n_pre tt_2 )
  **  (CharArray.full s_pre n_pre ss_2 )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) (i + 1 ) ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2 )) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ ((i + 1 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) (i + 1 ) ) ”
  &&  “ ((Zlength (ops_2)) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is_2 js_2 ) ”
  &&  “ (RepairState source target ss_2 tt_2 i ops ) ”
  &&  emp
).

Definition solver_entail_wit_9 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth j ss_2 0) <> (Znth i ss_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss_2 0)) /\ ((Znth k ss_2 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 0)) /\ ((Znth k_2 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2 )) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (CharArray.full s_pre n_pre ss_2 )
  **  (CharArray.full t_pre n_pre tt_2 )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) (j + 1 ) ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth j ss_2 0) <> (Znth i ss_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss_2 0)) /\ ((Znth k ss_2 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 0)) /\ ((Znth k_2 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2 )) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (source))) ”
  &&  “ (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) (j + 1 ) ) ”
  &&  “ ((Zlength (ops_2)) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is_2 js_2 ) ”
  &&  “ (RepairState source target ss_2 tt_2 i ops ) ”
  &&  emp
).

Definition solver_entail_wit_10 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2 )) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (CharArray.full s_pre n_pre ss_2 )
  **  (CharArray.full t_pre n_pre tt_2 )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) (i + 1 ) ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2 )) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ ((i + 1 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) (Zlength (source)) ) ”
  &&  “ (NoValueInRange tt_2 (Znth i ss_2 0) (i + 1 ) (i + 1 ) ) ”
  &&  “ ((Zlength (ops_2)) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is_2 js_2 ) ”
  &&  “ (RepairState source target ss_2 tt_2 i ops ) ”
  &&  emp
).

Definition solver_entail_wit_11 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth j tt_2 0) <> (Znth i ss_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss_2 0)) /\ ((Znth k ss_2 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 0)) /\ ((Znth k_2 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2 )) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (CharArray.full s_pre n_pre ss_2 )
  **  (CharArray.full t_pre n_pre tt_2 )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) (j + 1 ) ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth j tt_2 0) <> (Znth i ss_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss_2 0)) /\ ((Znth k ss_2 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 0)) /\ ((Znth k_2 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2 )) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ ((i + 1 ) <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (source))) ”
  &&  “ (NoValueInRange tt_2 (Znth i ss_2 0) (i + 1 ) (j + 1 ) ) ”
  &&  “ ((Zlength (ops_2)) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is_2 js_2 ) ”
  &&  “ (RepairState source target ss_2 tt_2 i ops ) ”
  &&  emp
).

Definition solver_entail_wit_12_1 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt_2 0) = (Znth i ss_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops_2)))) (PreH21 : (OperationLists ops_2 is_2 js_2 )) (PreH22 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (IntArray.full oj_pre ((m + 1 ) + 1 ) (app ((app (js_2) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is_2) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 0)) (ss_2)) 0)) ((replace_Znth (j) ((Znth j ss_2 0)) (tt_2)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 0)) (tt_2)) 0)) ((replace_Znth (j) ((Znth j tt_2 0)) (ss_2)))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= ((m + 1 ) + 1 )) ”
  &&  “ (((m + 1 ) + 1 ) <= (2 * (i + 1 ) )) ”
  &&  “ (((m + 1 ) + 1 ) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt (i + 1 ) ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre ((m + 1 ) + 1 ) is )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full oj_pre ((m + 1 ) + 1 ) js )
  **  (IntArray.undef_seg oj_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt_2 0) = (Znth i ss_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops_2)))) (PreH21 : (OperationLists ops_2 is_2 js_2 )) (PreH22 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 0)) (tt_2)) 0)) ((replace_Znth (j) ((Znth j tt_2 0)) (ss_2)))) 0)) /\ ((Znth k (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 0)) (tt_2)) 0)) ((replace_Znth (j) ((Znth j tt_2 0)) (ss_2)))) 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (source)))) -> ((97 <= (Znth k_2 (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 0)) (ss_2)) 0)) ((replace_Znth (j) ((Znth j ss_2 0)) (tt_2)))) 0)) /\ ((Znth k_2 (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 0)) (ss_2)) 0)) ((replace_Znth (j) ((Znth j ss_2 0)) (tt_2)))) 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ (0 <= (((Zlength (ops_2)) + 1 ) + 1 )) ”
  &&  “ ((((Zlength (ops_2)) + 1 ) + 1 ) <= (2 * (i + 1 ) )) ”
  &&  “ ((((Zlength (ops_2)) + 1 ) + 1 ) = (Zlength (ops))) ”
  &&  “ (OperationLists ops (app ((app (is_2) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) (app ((app (js_2) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((i + 1 )) ((@nil Z))))) ) ”
  &&  “ (RepairState source target (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 0)) (tt_2)) 0)) ((replace_Znth (j) ((Znth j tt_2 0)) (ss_2)))) (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 0)) (ss_2)) 0)) ((replace_Znth (j) ((Znth j ss_2 0)) (tt_2)))) (i + 1 ) ops ) ”
  &&  emp
).

Definition solver_entail_wit_12_2 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth i ss_2 0) = (Znth i tt_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss_2 0)) /\ ((Znth k ss_2 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 0)) /\ ((Znth k_2 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2 )) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (CharArray.full t_pre n_pre tt_2 )
  **  (CharArray.full s_pre n_pre ss_2 )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * (i + 1 ) )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt (i + 1 ) ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : ((Znth i ss_2 0) = (Znth i tt_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss_2 0)) /\ ((Znth k ss_2 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 0)) /\ ((Znth k_2 tt_2 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= m)) (PreH13 : (m <= (2 * i ))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2 )) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((Zlength (ops_2)) <= (2 * (i + 1 ) )) ”
  &&  “ ((Zlength (ops_2)) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is_2 js_2 ) ”
  &&  “ (RepairState source target ss_2 tt_2 (i + 1 ) ops ) ”
  &&  emp
).

Definition solver_entail_wit_12_3 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts_2: (@list Z)) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss_2 0) = (Znth i ss_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2 )) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2 )),
  (IntArray.full oj_pre (m + 1 ) (app (js_2) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is_2) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss_2 0)) (tt_2)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt_2 0)) (ss_2)) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (tt: (@list Z)) (ss: (@list Z)),
  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (m + 1 )) ”
  &&  “ ((m + 1 ) <= (2 * (i + 1 ) )) ”
  &&  “ ((m + 1 ) = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt (i + 1 ) ops ) ”
  &&  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre (m + 1 ) is )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oj_pre (m + 1 ) js )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt_2: (@list Z)) (ss_2: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss_2 0) = (Znth i ss_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 0)) /\ ((Znth k_3 ss_2 0) <= 122)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 0)) /\ ((Znth k_4 tt_2 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 0) <> (Znth i tt_2 0))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2 )) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2 )),
  TT && emp 
|--
  EX (ops: (@list (Z * Z))),
  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k (replace_Znth (j) ((Znth i tt_2 0)) (ss_2)) 0)) /\ ((Znth k (replace_Znth (j) ((Znth i tt_2 0)) (ss_2)) 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (source)))) -> ((97 <= (Znth k_2 (replace_Znth (i) ((Znth j ss_2 0)) (tt_2)) 0)) /\ ((Znth k_2 (replace_Znth (i) ((Znth j ss_2 0)) (tt_2)) 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ (0 <= ((Zlength (ops_2)) + 1 )) ”
  &&  “ (((Zlength (ops_2)) + 1 ) <= (2 * (i + 1 ) )) ”
  &&  “ (((Zlength (ops_2)) + 1 ) = (Zlength (ops))) ”
  &&  “ (OperationLists ops (app (is_2) ((cons ((j + 1 )) ((@nil Z))))) (app (js_2) ((cons ((i + 1 )) ((@nil Z))))) ) ”
  &&  “ (RepairState source target (replace_Znth (j) ((Znth i tt_2 0)) (ss_2)) (replace_Znth (i) ((Znth j ss_2 0)) (tt_2)) (i + 1 ) ops ) ”
  &&  emp
).

Definition solver_return_wit_1 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= m)) (PreH12 : (m <= (2 * i ))) (PreH13 : (m = (Zlength (ops_2)))) (PreH14 : (OperationLists ops_2 is_2 js_2 )) (PreH15 : (RepairState source target ss tt i ops_2 )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
|--
  EX (js: (@list Z)) (is: (@list Z)) (ops: (@list (Z * Z))) (out: (@option (@list (Z * Z)))),
  “ (Spec source target out ) ”
  &&  “ (out = (Some (ops))) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (1 <= (Zlength (ops))) ”
  &&  “ ((Zlength (ops)) <= (2 * n_pre )) ”
  &&  “ ((Zlength (is)) = (Zlength (ops))) ”
  &&  “ ((Zlength (js)) = (Zlength (ops))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (ops)))) -> (((Znth q is 0) = ((fst ((Znth q ops __default__Prod_Z_Z))) + 1 )) /\ ((Znth q js 0) = ((snd ((Znth q ops __default__Prod_Z_Z))) + 1 )))) ”
  &&  (CharArray.full_shape s_pre n_pre )
  **  (CharArray.full_shape t_pre n_pre )
  **  (IntArray.full oi_pre (Zlength (ops)) is )
  **  (IntArray.undef_seg oi_pre (Zlength (ops)) (2 * n_pre ) )
  **  (IntArray.full oj_pre (Zlength (ops)) js )
  **  (IntArray.undef_seg oj_pre (Zlength (ops)) (2 * n_pre ) )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= m)) (PreH12 : (m <= (2 * i ))) (PreH13 : (m = (Zlength (ops_2)))) (PreH14 : (OperationLists ops_2 is_2 js_2 )) (PreH15 : (RepairState source target ss tt i ops_2 )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
|--
  EX (js: (@list Z)) (is: (@list Z)) (ops: (@list (Z * Z))),
  “ (Spec source target (Some (ops)) ) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (1 <= (Zlength (ops))) ”
  &&  “ ((Zlength (ops)) <= (2 * n_pre )) ”
  &&  “ ((Zlength (is)) = (Zlength (ops))) ”
  &&  “ ((Zlength (js)) = (Zlength (ops))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (ops)))) -> (((Znth q is 0) = ((fst ((Znth q ops __default__Prod_Z_Z))) + 1 )) /\ ((Znth q js 0) = ((snd ((Znth q ops __default__Prod_Z_Z))) + 1 )))) ”
  &&  (CharArray.full_shape s_pre n_pre )
  **  (CharArray.full_shape t_pre n_pre )
  **  (IntArray.full oi_pre (Zlength (ops)) is )
  **  (IntArray.undef_seg oi_pre (Zlength (ops)) (2 * n_pre ) )
  **  (IntArray.full oj_pre (Zlength (ops)) js )
  **  (IntArray.undef_seg oj_pre (Zlength (ops)) (2 * n_pre ) )
).

Definition solver_return_wit_2 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2 )) (PreH21 : (RepairState source target ss tt i ops_2 )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
|--
  EX (oj_cells: (@list (@option Z))) (oi_cells: (@list (@option Z))) (out: (@option (@list (Z * Z)))),
  “ (Spec source target out ) ”
  &&  “ (out = None) ”
  &&  “ ((-1) = (-1)) ”
  &&  (CharArray.full_shape s_pre n_pre )
  **  (CharArray.full_shape t_pre n_pre )
  **  (IntArray.mixed_full oi_pre (2 * n_pre ) oi_cells )
  **  (IntArray.mixed_full oj_pre (2 * n_pre ) oj_cells )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (is_2: (@list Z)) (js_2: (@list Z)) (ops_2: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH15 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH16 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2 )) (PreH21 : (RepairState source target ss tt i ops_2 )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is_2 )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js_2 )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
|--
  EX (oj_cells: (@list (@option Z))) (oi_cells: (@list (@option Z))),
  “ (Spec source target None ) ”
  &&  (CharArray.full_shape s_pre n_pre )
  **  (CharArray.full_shape t_pre n_pre )
  **  (IntArray.mixed_full oi_pre (2 * n_pre ) oi_cells )
  **  (IntArray.mixed_full oj_pre (2 * n_pre ) oj_cells )
).

Definition solver_return_wit_3 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts )) (PreH9 : (CombinedOddAt source target c )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  EX (oj_cells: (@list (@option Z))) (oi_cells: (@list (@option Z))) (out: (@option (@list (Z * Z)))),
  “ (Spec source target out ) ”
  &&  “ (out = None) ”
  &&  “ ((-1) = (-1)) ”
  &&  (CharArray.full_shape s_pre n_pre )
  **  (CharArray.full_shape t_pre n_pre )
  **  (IntArray.mixed_full oi_pre (2 * n_pre ) oi_cells )
  **  (IntArray.mixed_full oj_pre (2 * n_pre ) oj_cells )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (Pre source target )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts )) (PreH9 : (CombinedOddAt source target c )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  EX (oj_cells: (@list (@option Z))) (oi_cells: (@list (@option Z))),
  “ (Spec source target None ) ”
  &&  (CharArray.full_shape s_pre n_pre )
  **  (CharArray.full_shape t_pre n_pre )
  **  (IntArray.mixed_full oi_pre (2 * n_pre ) oi_cells )
  **  (IntArray.mixed_full oj_pre (2 * n_pre ) oj_cells )
).

Definition solver_partial_solve_wit_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (CountedPrefix source target i counts ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i source 0))
  **  (CharArray.missing_i s_pre i 0 n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (CountedPrefix source target i counts ) ”
  &&  (((( &( "cnt" ) ) + (((Znth i source 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i source 0) - 97 ) counts 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i source 0) - 97 ) 0 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
.

Definition solver_partial_solve_wit_3 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (CountedPrefix source target i counts ) ”
  &&  (((( &( "cnt" ) ) + (((Znth i source 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i source 0) - 97 ) 0 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
.

Definition solver_partial_solve_wit_4 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (CountedPrefix source target i counts ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i target 0))
  **  (CharArray.missing_i t_pre i 0 n_pre target )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full s_pre n_pre source )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
.

Definition solver_partial_solve_wit_5 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (CharArray.full t_pre n_pre target )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full s_pre n_pre source )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (CountedPrefix source target i counts ) ”
  &&  (((( &( "cnt" ) ) + (((Znth i target 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i target 0) - 97 ) (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i target 0) - 97 ) 0 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
.

Definition solver_partial_solve_wit_6 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts )),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (CountedPrefix source target i counts ) ”
  &&  (((( &( "cnt" ) ) + (((Znth i target 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i target 0) - 97 ) 0 26 (replace_Znth (((Znth i source 0) - 97 )) (((Znth ((Znth i source 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full t_pre n_pre target )
  **  (CharArray.full s_pre n_pre source )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
.

Definition solver_partial_solve_wit_7 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (c: Z) (PreH1 : (c < 26)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts )) (PreH12 : (CountsEvenBefore counts c )),
  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (c < 26) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 26) ”
  &&  “ (CountedPrefix source target n_pre counts ) ”
  &&  “ (CountsEvenBefore counts c ) ”
  &&  (((( &( "cnt" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c counts 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) c 0 26 counts )
  **  (CharArray.full s_pre n_pre source )
  **  (CharArray.full t_pre n_pre target )
  **  (IntArray.undef_full oi_pre (2 * n_pre ) )
  **  (IntArray.undef_full oj_pre (2 * n_pre ) )
.

Definition solver_partial_solve_wit_8 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= m)) (PreH12 : (m <= (2 * i ))) (PreH13 : (m = (Zlength (ops)))) (PreH14 : (OperationLists ops is js )) (PreH15 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i ss 0))
  **  (CharArray.missing_i s_pre i 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_9 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= m)) (PreH12 : (m <= (2 * i ))) (PreH13 : (m = (Zlength (ops)))) (PreH14 : (OperationLists ops is js )) (PreH15 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (i < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i tt 0))
  **  (CharArray.missing_i t_pre i 0 n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_10 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH14 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH15 : (0 <= m)) (PreH16 : (m <= (2 * i ))) (PreH17 : (m = (Zlength (ops)))) (PreH18 : (OperationLists ops is js )) (PreH19 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j ss 0))
  **  (CharArray.missing_i s_pre j 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_11 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH14 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH15 : (0 <= m)) (PreH16 : (m <= (2 * i ))) (PreH17 : (m = (Zlength (ops)))) (PreH18 : (OperationLists ops is js )) (PreH19 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i ss 0))
  **  (CharArray.missing_i s_pre i 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_12 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j ss 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j ss 0))
  **  (CharArray.missing_i s_pre j 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_13 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j ss 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i tt 0))
  **  (CharArray.missing_i t_pre i 0 n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_14 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j ss 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i s_pre j 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_15 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j ss 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i t_pre i 0 n_pre tt )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_16 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j ss 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((oi_pre + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_17 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) j )) (PreH17 : (0 <= m)) (PreH18 : (m <= (2 * i ))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js )) (PreH21 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j ss 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((oj_pre + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt 0)) (ss)) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_18 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH14 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH15 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js )) (PreH20 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j tt 0))
  **  (CharArray.missing_i t_pre j 0 n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_19 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH14 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH15 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH16 : (0 <= m)) (PreH17 : (m <= (2 * i ))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js )) (PreH20 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i ss 0))
  **  (CharArray.missing_i s_pre i 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_20 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j ss 0))
  **  (CharArray.missing_i s_pre j 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_21 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j tt 0))
  **  (CharArray.missing_i t_pre j 0 n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_22 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre tt )
  **  (CharArray.full s_pre n_pre ss )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i s_pre j 0 n_pre ss )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_23 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (CharArray.full t_pre n_pre tt )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i t_pre j 0 n_pre tt )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_24 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.undef_seg oi_pre m (2 * n_pre ) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((oi_pre + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oi_pre m is )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_25 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.undef_seg oj_pre m (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((oj_pre + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oj_pre m js )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_26 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0))
  **  (CharArray.missing_i s_pre j 0 n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_27 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0))
  **  (CharArray.missing_i t_pre i 0 n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_28 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i s_pre j 0 n_pre (replace_Znth (j) ((Znth j tt 0)) (ss)) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_29 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (CharArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i t_pre i 0 n_pre (replace_Znth (j) ((Znth j ss 0)) (tt)) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_30 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((oi_pre + ((m + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre (m + 1 ) (app (is) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_31 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (oi_pre: Z) (oj_pre: Z) (counts: (@list Z)) (is: (@list Z)) (js: (@list Z)) (ops: (@list (Z * Z))) (m: Z) (j: Z) (i: Z) (tt: (@list Z)) (ss: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt 0) = (Znth i ss 0))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss 0) <> (Znth i tt 0))) (PreH16 : (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre )) (PreH17 : (NoValueInRange tt (Znth i ss 0) (i + 1 ) j )) (PreH18 : (0 <= m)) (PreH19 : (m <= (2 * i ))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js )) (PreH22 : (RepairState source target ss tt i ops )),
  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oj_pre (m + 1 ) (2 * n_pre ) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (j < n_pre) ”
  &&  “ ((Znth j tt 0) = (Znth i ss 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (Pre source target ) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 50) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k ss 0)) /\ ((Znth k ss 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt 0)) /\ ((Znth k_2 tt 0) <= 122))) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ ((Zlength (target)) = n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((i + 1 ) <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ ((Znth i ss 0) <> (Znth i tt 0)) ”
  &&  “ (NoValueInRange ss (Znth i ss 0) (i + 1 ) n_pre ) ”
  &&  “ (NoValueInRange tt (Znth i ss 0) (i + 1 ) j ) ”
  &&  “ (0 <= m) ”
  &&  “ (m <= (2 * i )) ”
  &&  “ (m = (Zlength (ops))) ”
  &&  “ (OperationLists ops is js ) ”
  &&  “ (RepairState source target ss tt i ops ) ”
  &&  (((oj_pre + ((m + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg oj_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full oi_pre ((m + 1 ) + 1 ) (app ((app (is) ((cons ((j + 1 )) ((@nil Z)))))) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg oi_pre ((m + 1 ) + 1 ) (2 * n_pre ) )
  **  (CharArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt 0)) (ss)) 0)) ((replace_Znth (j) ((Znth j ss 0)) (tt)))) )
  **  (CharArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss 0)) (tt)) 0)) ((replace_Znth (j) ((Znth j tt 0)) (ss)))) )
  **  (IntArray.full oj_pre (m + 1 ) (app (js) ((cons ((j + 1 )) ((@nil Z))))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
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
