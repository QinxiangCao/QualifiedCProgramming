From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_copyd -----*)

Definition mpn_copyd_safety_wit_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((False \/ (True /\ (off_shifted = 0))) \/ (True /\ (off_shifted > 0))) ”
.

Definition mpn_copyd_safety_wit_2_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_copyd_safety_wit_3_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_copyd_safety_wit_4_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (off_shifted = 0)) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = s_pre)) (PreH10 : (d_pre = s_pre)) (PreH11 : (off_shifted = 0)) (PreH12 : (n = (n_pre - 1 ))) (PreH13 : (n_pre >= 0)) (PreH14 : ((Zlength (l_shifted)) = n_pre)) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyd_safety_wit_5_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((-1) <= n_2)) (PreH4 : (n_2 < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (k_2 <= (n_2 + 1 ))) (PreH8 : ((n_2 + 1 ) <= k_2)) (PreH9 : (0 <= k_2)) (PreH10 : (k_2 <= n_pre)) (PreH11 : ((Zlength (l_shifted)) = n_pre)) (PreH12 : (list_within_bound UINT_MOD l_shifted )) (PreH13 : (off_shifted > 0)) (PreH14 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH15 : (n = (n_pre - 1 ))) (PreH16 : (n_pre >= 0)) (PreH17 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH18 : (k = n_pre)) (PreH19 : (k <= (n + 1 ))) (PreH20 : ((n + 1 ) <= k)) (PreH21 : ((Zlength (l_shifted)) = n_pre)) (PreH22 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyd_safety_wit_6_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n_2: Z) (n: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n)) (PreH7 : (n < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n_2 = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> s_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_copyd_safety_wit_7_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n)) (PreH12 : (n < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (((d_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth (n - n ) (sublist (n) ((n + 1 )) (l_shifted)) 0))
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_copyd_entail_wit_1_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
|--
  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  TT && emp 
|--
  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  emp
).

Definition mpn_copyd_entail_wit_1_off_zero_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  (d_pre = s_pre)
.

Definition mpn_copyd_entail_wit_1_off_zero_split_goal_2 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  (d_pre = s_pre)
.

Definition mpn_copyd_entail_wit_2_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
|--
  EX (k: Z),
  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (k = n_pre) ”
  &&  “ (k <= ((n_pre - 1 ) + 1 )) ”
  &&  “ (((n_pre - 1 ) + 1 ) <= k) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k (sublist (0) (k) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k (off_shifted + k ) )
  **  (UIntArray.seg d_pre k n_pre (sublist (k) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  TT && emp 
|--
  “ ((sublist (n_pre) (n_pre) (l_shifted)) = (@nil Z)) ”
  &&  emp
).

Definition mpn_copyd_entail_wit_2_off_pos_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  ((sublist (n_pre) (n_pre) (l_shifted)) = (@nil Z))
.

Definition mpn_copyd_entail_wit_3_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (off_shifted = 0)) (PreH4 : (n = (n_pre - 1 ))) (PreH5 : (n_pre >= 0)) (PreH6 : ((Zlength (l_shifted)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_4_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH3 : (n = (n_pre - 1 ))) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (k = n_pre)) (PreH7 : (k <= (n + 1 ))) (PreH8 : ((n + 1 ) <= k)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k (sublist (0) (k) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k (off_shifted + k ) )
  **  (UIntArray.seg d_pre k n_pre (sublist (k) (n_pre) (l_shifted)) )
|--
  EX (k_2: Z),
  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (k_2 <= (n + 1 )) ”
  &&  “ ((n + 1 ) <= k_2) ”
  &&  “ (0 <= k_2) ”
  &&  “ (k_2 <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (k = n_pre) ”
  &&  “ (k <= (n + 1 )) ”
  &&  “ ((n + 1 ) <= k) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_5_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n_2: Z) (k_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n + 1 ))) (PreH9 : ((n + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n_2 = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n_2 + 1 ))) (PreH21 : ((n_2 + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n_2: Z) (k_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n + 1 ))) (PreH9 : ((n + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n_2 = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n_2 + 1 ))) (PreH21 : ((n_2 + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_entail_wit_5_off_pos_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n_2: Z) (k_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n + 1 ))) (PreH9 : ((n + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n_2 = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n_2 + 1 ))) (PreH21 : ((n_2 + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_6_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ ((-1) <= (n_2 - 1 )) ”
  &&  “ ((n_2 - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_entail_wit_6_off_zero_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_7_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n_2: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n_2)) (PreH4 : (n_2 < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n_2)) (PreH12 : (n_2 < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (((d_pre + (n_2 * sizeof(UINT)))) # UInt  |-> (Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0))
  **  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n_2 + 1 ) (off_shifted + n_2 ) )
  **  (UIntArray.seg d_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  EX (k_2: Z) (k: Z) (n: Z),
  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((-1) <= (n_2 - 1 )) ”
  &&  “ ((n_2 - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (k_2 <= ((n_2 - 1 ) + 1 )) ”
  &&  “ (((n_2 - 1 ) + 1 ) <= k_2) ”
  &&  “ (0 <= k_2) ”
  &&  “ (k_2 <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (k = n_pre) ”
  &&  “ (k <= (n + 1 )) ”
  &&  “ ((n + 1 ) <= k) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n_2: Z) (PreH1 : ((Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0) <= UINT_MAX)) (PreH2 : ((Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0) >= 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (off_shifted > 0)) (PreH5 : (0 <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (off_shifted > 0)) (PreH13 : (0 <= n_2)) (PreH14 : (n_2 < n_pre)) (PreH15 : (n_pre >= 0)) (PreH16 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH17 : ((Zlength (l_shifted)) = n_pre)) (PreH18 : (list_within_bound UINT_MOD l_shifted )),
  (((d_pre + (n_2 * sizeof(UINT)))) # UInt  |-> (Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0))
  **  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n_2 + 1 ) (off_shifted + n_2 ) )
  **  (UIntArray.seg d_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  EX (k_2: Z),
  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((-1) <= (n_2 - 1 )) ”
  &&  “ ((n_2 - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (k_2 <= ((n_2 - 1 ) + 1 )) ”
  &&  “ (((n_2 - 1 ) + 1 ) <= k_2) ”
  &&  “ (0 <= k_2) ”
  &&  “ (k_2 <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (n_pre <= ((n_pre - 1 ) + 1 )) ”
  &&  “ (((n_pre - 1 ) + 1 ) <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_return_wit_1_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.undef_seg s_pre 0 off_shifted )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  (UIntArray.undef_seg s_pre 0 off_shifted )
).

Definition mpn_copyd_return_wit_1_off_zero_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  (UIntArray.undef_seg s_pre 0 off_shifted )
.

Definition mpn_copyd_return_wit_2_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n_2 + 1 ))) (PreH9 : ((n_2 + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n + 1 ))) (PreH21 : ((n + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.undef_seg s_pre 0 off_shifted )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n_2 + 1 ))) (PreH9 : ((n_2 + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n + 1 ))) (PreH21 : ((n + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_return_wit_2_off_pos_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n_2 + 1 ))) (PreH9 : ((n_2 + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n + 1 ))) (PreH21 : ((n + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.full s_pre n_pre l_shifted )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre >= 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.full s_pre n_pre l_shifted )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
.

Definition mpn_copyd_partial_solve_wit_2_off_zero_pure :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n)) (PreH6 : (n < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n_2 = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (s_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
.

Definition mpn_copyd_partial_solve_wit_2_off_zero_aux :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n)) (PreH6 : (n < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n_2 = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (s_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n >= 0) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_2 = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "d" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_2_off_zero := mpn_copyd_partial_solve_wit_2_off_zero_pure -> mpn_copyd_partial_solve_wit_2_off_zero_aux.

Definition mpn_copyd_partial_solve_wit_3_off_pos_pure :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
.

Definition mpn_copyd_partial_solve_wit_3_off_pos_aux :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_3_off_pos := mpn_copyd_partial_solve_wit_3_off_pos_pure -> mpn_copyd_partial_solve_wit_3_off_pos_aux.

Definition mpn_copyd_partial_solve_wit_4_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (s_pre = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (n_2 >= 0)) (PreH4 : (d_pre = s_pre)) (PreH5 : (d_pre = s_pre)) (PreH6 : (off_shifted = 0)) (PreH7 : ((-1) <= n_2)) (PreH8 : (n_2 < n_pre)) (PreH9 : (n_pre >= 0)) (PreH10 : ((Zlength (l_shifted)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_shifted )) (PreH12 : (d_pre = s_pre)) (PreH13 : (d_pre = s_pre)) (PreH14 : (off_shifted = 0)) (PreH15 : (n = (n_pre - 1 ))) (PreH16 : (n_pre >= 0)) (PreH17 : ((Zlength (l_shifted)) = n_pre)) (PreH18 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ”
  &&  “ (n_2 >= 0) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ ((-1) <= n_2) ”
  &&  “ (n_2 < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (n_2 * sizeof(UINT)))) # UInt  |-> (Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i s_pre n_2 n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_5_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ”
  &&  “ (n_2 >= 0) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ ((-1) <= n_2) ”
  &&  “ (n_2 < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n = (n_pre - 1 )) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (n_2 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i s_pre n_2 n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_6_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n)) (PreH12 : (n < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth (n - n ) (sublist (n) ((n + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i s_pre n n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_7_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n)) (PreH12 : (n < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (n * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_which_implies_wit_1 :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (s: Z),
  (UIntArray.full s n l_shifted )
  **  (UIntArray.undef_seg s n (n + off_shifted ) )
|--
  (UIntArray.seg s 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s n (n + off_shifted ) )
) \/
(
forall (l_shifted: (@list Z)) (n: Z) (s: Z),
  (UIntArray.full s n l_shifted )
|--
  (UIntArray.seg s 0 n (sublist (0) (n) (l_shifted)) )
).

Definition mpn_copyd_which_implies_wit_1_split_goal_spatial :=
forall (l_shifted: (@list Z)) (n: Z) (s: Z),
  (UIntArray.full s n l_shifted )
|--
  (UIntArray.seg s 0 n (sublist (0) (n) (l_shifted)) )
.

Definition mpn_copyd_which_implies_wit_2 :=
(
forall (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (d: Z) (n: Z) (PreH1 : (d = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (d = s_pre) ”
  &&  “ (d_pre = s_pre) ”
  &&  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (d: Z) (n: Z) (PreH1 : (d = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_which_implies_wit_2_split_goal_spatial :=
forall (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (d: Z) (n: Z) (PreH1 : (d = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)),
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_which_implies_wit_3 :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  “ ((sublist (0) ((n + 1 )) (l_shifted)) = (app ((sublist (0) (n) (l_shifted))) ((sublist (n) ((n + 1 )) (l_shifted))))) ”
  &&  “ ((Zlength ((sublist (0) (n) (l_shifted)))) = (n - 0 )) ”
  &&  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
).

Definition mpn_copyd_which_implies_wit_3_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  “ ((sublist (0) ((n + 1 )) (l_shifted)) = (app ((sublist (0) (n) (l_shifted))) ((sublist (n) ((n + 1 )) (l_shifted))))) ”
.

Definition mpn_copyd_which_implies_wit_3_split_goal_2 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  “ ((Zlength ((sublist (0) (n) (l_shifted)))) = (n - 0 )) ”
.

Definition mpn_copyd_which_implies_wit_3_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
.

(*----- Function mpn_zero -----*)

Definition mpn_zero_safety_wit_1 :=
forall (rp_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_zero_safety_wit_2 :=
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : ((-1) <= n)) (PreH2 : (n < n_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH5 : (list_within_bound UINT_MOD l_done )) (PreH6 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_zero_safety_wit_3 :=
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.undef_seg rp_pre n (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_zero_safety_wit_4 :=
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  (((rp_pre + (n * sizeof(UINT)))) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_zero_entail_wit_1 :=
(
forall (rp_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)),
  (UIntArray.undef_seg rp_pre 0 n_pre )
|--
  EX (l_done: (@list Z)),
  “ ((-1) <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((n_pre - 1 ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (rp_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)),
  TT && emp 
|--
  EX (l_done: (@list Z)),
  “ ((-1) <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
).

Definition mpn_zero_entail_wit_2 :=
(
forall (rp_pre: Z) (n_pre: Z) (l_done_2: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done_2)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done_2)) = 0)),
  (((rp_pre + (n * sizeof(UINT)))) # UInt  |-> 0)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done_2 )
|--
  EX (l_done: (@list Z)),
  “ ((-1) <= (n - 1 )) ”
  &&  “ ((n - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((n - 1 ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (rp_pre: Z) (n_pre: Z) (l_done_2: (@list Z)) (n: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((Zlength (l_done_2)) = (n_pre - (n + 1 ) ))) (PreH8 : (list_within_bound UINT_MOD l_done_2 )) (PreH9 : ((list_to_Z (UINT_MOD) (l_done_2)) = 0)),
  (((rp_pre + (n * sizeof(UINT)))) # UInt  |-> 0)
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done_2 )
|--
  EX (l_done: (@list Z)),
  “ ((-1) <= (n - 1 )) ”
  &&  “ ((n - 1 ) < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.seg rp_pre ((n - 1 ) + 1 ) n_pre l_done )
).

Definition mpn_zero_return_wit_1 :=
(
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  EX (l: (@list Z)),
  “ ((Zlength (l)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  (UIntArray.full rp_pre n_pre l )
) \/
(
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  EX (l: (@list Z)),
  “ ((Zlength (l)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  (UIntArray.full rp_pre n_pre l )
).

Definition mpn_zero_partial_solve_wit_1 :=
forall (rp_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)),
  (UIntArray.undef_seg rp_pre 0 n_pre )
|--
  “ (n_pre >= 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  (UIntArray.undef_seg rp_pre 0 n_pre )
.

Definition mpn_zero_partial_solve_wit_2_pure :=
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
.

Definition mpn_zero_partial_solve_wit_2_aux :=
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n >= 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (n + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
.

Definition mpn_zero_partial_solve_wit_2 := mpn_zero_partial_solve_wit_2_pure -> mpn_zero_partial_solve_wit_2_aux.

Definition mpn_zero_partial_solve_wit_3 :=
forall (rp_pre: Z) (n_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)),
  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.undef_seg rp_pre n (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (n >= 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (n + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (((rp_pre + (n * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
.

Definition mpn_zero_which_implies_wit_1 :=
forall (n: Z) (rp: Z),
  (UIntArray.undef_seg rp 0 n )
|--
  (UIntArray.undef_seg rp 0 n )
.

Definition mpn_zero_which_implies_wit_2 :=
forall (rp_pre: Z) (n_pre: Z) (n: Z) (PreH1 : (0 <= n)) (PreH2 : (n < n_pre)),
  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
|--
  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.undef_seg rp_pre n (n + 1 ) )
.

(*----- Function mpz_mul_2exp -----*)

Definition mpz_mul_2exp_safety_wit_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_3 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_mul_2exp_safety_wit_4 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_mul_2exp_safety_wit_5 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_mul_2exp_safety_wit_6 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_mul_2exp_safety_wit_7 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
).

Definition mpz_mul_2exp_safety_wit_7_split_goal_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
.

Definition mpz_mul_2exp_safety_wit_7_split_goal_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
.

Definition mpz_mul_2exp_safety_wit_8 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) ”
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) ”
).

Definition mpz_mul_2exp_safety_wit_8_split_goal_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
.

Definition mpz_mul_2exp_safety_wit_8_split_goal_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) ”
.

Definition mpz_mul_2exp_safety_wit_9 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
).

Definition mpz_mul_2exp_safety_wit_9_split_goal_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_mul_2exp_safety_wit_9_split_goal_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
.

Definition mpz_mul_2exp_safety_wit_10 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_11 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size: Z) (cap: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq size )) (PreH2 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)))) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_12 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size: Z) (cap: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq size )) (PreH2 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)))) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_13 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size: Z) (cap: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (same_sign z_eq size )) (PreH3 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ False ”
.

Definition mpz_mul_2exp_safety_wit_14 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size: Z) (cap: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (same_sign z_eq size )) (PreH3 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ False ”
.

Definition mpz_mul_2exp_safety_wit_15 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (rn - 1 )) ”
.

Definition mpz_mul_2exp_safety_wit_16 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_2exp_safety_wit_17 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val = 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (rn - 1 )) ”
.

Definition mpz_mul_2exp_safety_wit_18 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val <> 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (rn - 0 )) ”
.

Definition mpz_mul_2exp_safety_wit_19 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_20 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 0 ) <> (INT_MIN)) ”
.

Definition mpz_mul_2exp_safety_wit_21 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = limbs)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH4 : (cy_val <> 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift > 0)) (PreH16 : (1 <= shift)) (PreH17 : (shift < 32)) (PreH18 : (rn = ((un + limbs ) + 1 ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l_in)) = un)) (PreH22 : (list_within_bound UINT_MOD l_in )) (PreH23 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH24 : ((last (l_in) (1)) >= 1)) (PreH25 : ((Zlength (l_out)) = un)) (PreH26 : (list_within_bound UINT_MOD l_out )) (PreH27 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH28 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH29 : (u__mp_d = rp)) (PreH30 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_22 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 1 ) <> (INT_MIN)) ”
.

Definition mpz_mul_2exp_safety_wit_23 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = limbs)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH4 : (cy_val = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift > 0)) (PreH16 : (1 <= shift)) (PreH17 : (shift < 32)) (PreH18 : (rn = ((un + limbs ) + 1 ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l_in)) = un)) (PreH22 : (list_within_bound UINT_MOD l_in )) (PreH23 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH24 : ((last (l_in) (1)) >= 1)) (PreH25 : ((Zlength (l_out)) = un)) (PreH26 : (list_within_bound UINT_MOD l_out )) (PreH27 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH28 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH29 : (u__mp_d = rp)) (PreH30 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_24 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l_2 )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (rn <> (INT_MIN)) ”
.

Definition mpz_mul_2exp_safety_wit_25 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : ((Zlength (l_2)) = limbs)) (PreH2 : (list_within_bound UINT_MOD l_2 )) (PreH3 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (un = (Zabs (size)))) (PreH10 : (un > 0)) (PreH11 : (limbs = (bits_pre ÷ 32 ))) (PreH12 : (limbs >= 0)) (PreH13 : (shift = (bits_pre % ( 32 ) ))) (PreH14 : (shift = 0)) (PreH15 : (rn = (un + limbs ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l)) = un)) (PreH19 : (list_within_bound UINT_MOD l )) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH21 : ((last (l) (1)) >= 1)) (PreH22 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH23 : (u__mp_d = rp)) (PreH24 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l_2 )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_entail_wit_1 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )),
  (store_Z r_pre z_eq )
|--
  EX (ptr: Z) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )),
  (store_Z r_pre z_eq )
|--
  EX (ptr: Z) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
).

Definition mpz_mul_2exp_entail_wit_2 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (same_sign z_eq size_2 )) (PreH3 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size_2)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z) (u__mp_alloc: Z) (l: (@list Z)) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (retval > 0) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0) ”
  &&  “ (1 <= (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32))) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) < 32) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) = ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = retval) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap))) ”
  &&  “ (u__mp_d = retval_2) ”
  &&  “ (retval_2 = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d retval l )
  **  (UIntArray.undef_seg u__mp_d retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg u__mp_d (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (z__mp_alloc <= INT_MAX)) (PreH2 : (size_2 <= INT_MAX)) (PreH3 : (z__mp_alloc >= INT_MIN)) (PreH4 : (size_2 >= INT_MIN)) (PreH5 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH6 : (same_sign z_eq size_2 )) (PreH7 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)))) (PreH8 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Zabs (size_2)))) (PreH11 : (r_pre = u_pre)) (PreH12 : (bits_pre >= 0)) (PreH13 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH14 : (same_sign z_eq size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z)) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (retval > 0) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0) ”
  &&  “ (1 <= (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32))) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) < 32) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = retval) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 retval l )
  **  (UIntArray.undef_seg retval_2 retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg retval_2 (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
).

Definition mpz_mul_2exp_entail_wit_3 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l: (@list Z)) (size_2: Z) (cap_2: Z) (l_out_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out_2)) = un)) (PreH2 : (list_within_bound UINT_MOD l_out_2 )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out_2)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((list_to_Z (UINT_MOD) (l)) * (Z.pow (2) (shift)) ))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (un = (Zabs (size_2)))) (PreH10 : (un > 0)) (PreH11 : (limbs = (bits_pre ÷ 32 ))) (PreH12 : (limbs >= 0)) (PreH13 : (shift = (bits_pre % ( 32 ) ))) (PreH14 : (shift > 0)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (rn = ((un + limbs ) + 1 ))) (PreH18 : (rn <= INT_MAX)) (PreH19 : ((un + limbs ) <= INT_MAX)) (PreH20 : ((Zlength (l)) = un)) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH25 : (u__mp_d_2 = rp)) (PreH26 : (rp = u__mp_d_2)),
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d_2)
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (u__mp_d: Z) (u__mp_alloc: Z) (l_out: (@list Z)) (l_in: (@list Z)) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l: (@list Z)) (size_2: Z) (cap_2: Z) (l_out_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out_2)) = un)) (PreH2 : (list_within_bound UINT_MOD l_out_2 )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out_2)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((list_to_Z (UINT_MOD) (l)) * (Z.pow (2) (shift)) ))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (un = (Zabs (size_2)))) (PreH10 : (un > 0)) (PreH11 : (limbs = (bits_pre ÷ 32 ))) (PreH12 : (limbs >= 0)) (PreH13 : (shift = (bits_pre % ( 32 ) ))) (PreH14 : (shift > 0)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (rn = ((un + limbs ) + 1 ))) (PreH18 : (rn <= INT_MAX)) (PreH19 : ((un + limbs ) <= INT_MAX)) (PreH20 : ((Zlength (l)) = un)) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH25 : (u__mp_d_2 = rp)) (PreH26 : (rp = u__mp_d_2)),
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (l_in: (@list Z)) (cap: Z),
  “ (u__mp_d_2 = rp) ”
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d_2 = rp) ”
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  “ (un = (Zabs (size_2))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out_2)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out_2 ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out_2)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
).

Definition mpz_mul_2exp_entail_wit_4 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (same_sign z_eq size_2 )) (PreH3 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size_2)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z) (u__mp_alloc: Z) (l: (@list Z)) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (retval > 0) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = 0) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) = (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = retval) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap))) ”
  &&  “ (u__mp_d = retval_2) ”
  &&  “ (retval_2 = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d retval l )
  **  (UIntArray.undef_seg u__mp_d retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg u__mp_d (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (z__mp_alloc <= INT_MAX)) (PreH2 : (size_2 <= INT_MAX)) (PreH3 : (z__mp_alloc >= INT_MIN)) (PreH4 : (size_2 >= INT_MIN)) (PreH5 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH6 : (same_sign z_eq size_2 )) (PreH7 : (z__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)))) (PreH8 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Zabs (size_2)))) (PreH11 : (r_pre = u_pre)) (PreH12 : (bits_pre >= 0)) (PreH13 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH14 : (same_sign z_eq size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z)) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (retval > 0) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ”
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = 0) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) = (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = retval) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 retval l )
  **  (UIntArray.undef_seg retval_2 retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg retval_2 (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
).

Definition mpz_mul_2exp_entail_wit_5 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l_2: (@list Z)) (size_2: Z) (cap_2: Z) (PreH1 : ((rp + (limbs * sizeof(UINT))) = (u__mp_d_2 + (limbs * sizeof(UINT))))) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (un = (Zabs (size_2)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift = 0)) (PreH13 : (rn = (un + limbs ))) (PreH14 : (rn <= INT_MAX)) (PreH15 : ((un + limbs ) <= INT_MAX)) (PreH16 : ((Zlength (l_2)) = un)) (PreH17 : (list_within_bound UINT_MOD l_2 )) (PreH18 : ((list_to_Z (UINT_MOD) (l_2)) = (Zabs (z_eq)))) (PreH19 : ((last (l_2) (1)) >= 1)) (PreH20 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH21 : (u__mp_d_2 = rp)) (PreH22 : (rp = u__mp_d_2)),
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l_2)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d_2)
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (u__mp_d: Z) (u__mp_alloc: Z) (l: (@list Z)) (cap: Z) (size: Z),
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift = 0) ”
  &&  “ (rn = (un + limbs )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l_2: (@list Z)) (size_2: Z) (cap_2: Z) (PreH1 : ((rp + (limbs * sizeof(UINT))) = (u__mp_d_2 + (limbs * sizeof(UINT))))) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (un = (Zabs (size_2)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift = 0)) (PreH13 : (rn = (un + limbs ))) (PreH14 : (rn <= INT_MAX)) (PreH15 : ((un + limbs ) <= INT_MAX)) (PreH16 : ((Zlength (l_2)) = un)) (PreH17 : (list_within_bound UINT_MOD l_2 )) (PreH18 : ((list_to_Z (UINT_MOD) (l_2)) = (Zabs (z_eq)))) (PreH19 : ((last (l_2) (1)) >= 1)) (PreH20 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH21 : (u__mp_d_2 = rp)) (PreH22 : (rp = u__mp_d_2)),
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (l: (@list Z)) (cap: Z),
  “ ((sublist (0) (un) (l_2)) = (sublist (0) (un) (l))) ”
  &&  “ (u__mp_d_2 = rp) ”
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d_2 = rp) ”
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  “ (un = (Zabs (size_2))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift = 0) ”
  &&  “ (rn = (un + limbs )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
).

Definition mpz_mul_2exp_return_wit_1 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (cap >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z) (ptr_2: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) 0 ) ”
  &&  “ ((Zabs (0)) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs (0)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_2 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-(rn - 0 )))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size < 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val <> 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (-(rn - 0 )) ) ”
  &&  “ ((Zabs ((-(rn - 0 )))) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((-(rn - 0 )))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((-(rn - 0 )))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_3 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (rn - 0 ))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size >= 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val <> 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (rn - 0 ) ) ”
  &&  “ ((Zabs ((rn - 0 ))) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((rn - 0 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((rn - 0 ))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_4 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-(rn - 1 )))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size < 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val = 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (-(rn - 1 )) ) ”
  &&  “ ((Zabs ((-(rn - 1 )))) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((-(rn - 1 )))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((-(rn - 1 )))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_5 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (rn - 1 ))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size >= 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val = 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (rn - 1 ) ) ”
  &&  “ ((Zabs ((rn - 1 ))) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((rn - 1 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((rn - 1 ))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_6 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn))
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (size < 0)) (PreH4 : ((Zlength (l_2)) = limbs)) (PreH5 : (list_within_bound UINT_MOD l_2 )) (PreH6 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (un = (Zabs (size)))) (PreH13 : (un > 0)) (PreH14 : (limbs = (bits_pre ÷ 32 ))) (PreH15 : (limbs >= 0)) (PreH16 : (shift = (bits_pre % ( 32 ) ))) (PreH17 : (shift = 0)) (PreH18 : (rn = (un + limbs ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l)) = un)) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH24 : ((last (l) (1)) >= 1)) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (-rn) ) ”
  &&  “ ((Zabs ((-rn))) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((-rn))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((-rn))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_7 :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn)
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (size >= 0)) (PreH4 : ((Zlength (l_2)) = limbs)) (PreH5 : (list_within_bound UINT_MOD l_2 )) (PreH6 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (un = (Zabs (size)))) (PreH13 : (un > 0)) (PreH14 : (limbs = (bits_pre ÷ 32 ))) (PreH15 : (limbs >= 0)) (PreH16 : (shift = (bits_pre % ( 32 ) ))) (PreH17 : (shift = 0)) (PreH18 : (rn = (un + limbs ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l)) = un)) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH24 : ((last (l) (1)) >= 1)) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) rn ) ”
  &&  “ ((Zabs (rn)) <= cap_2) ”
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs (rn)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs (rn)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_partial_solve_wit_1_pure :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : (size >= INT_MIN)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_mul_2exp_partial_solve_wit_1_pure_split_goal_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : (size >= INT_MIN)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_mul_2exp_partial_solve_wit_1_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_mul_2exp_partial_solve_wit_1 := mpz_mul_2exp_partial_solve_wit_1_pure -> mpz_mul_2exp_partial_solve_wit_1_aux.

Definition mpz_mul_2exp_partial_solve_wit_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (retval = 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_mul_2exp_partial_solve_wit_3_pure :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (cap >= 0) ”
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH7 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH12 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (r_pre = u_pre)) (PreH18 : (bits_pre >= 0)) (PreH19 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH20 : (same_sign z_eq size )) (PreH21 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
).

Definition mpz_mul_2exp_partial_solve_wit_3_pure_split_goal_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH7 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH12 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (r_pre = u_pre)) (PreH18 : (bits_pre >= 0)) (PreH19 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH20 : (same_sign z_eq size )) (PreH21 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_3_pure_split_goal_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH7 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH12 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (r_pre = u_pre)) (PreH18 : (bits_pre >= 0)) (PreH19 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH20 : (same_sign z_eq size )) (PreH21 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_3_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (cap >= 0) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_mul_2exp_partial_solve_wit_3 := mpz_mul_2exp_partial_solve_wit_3_pure -> mpz_mul_2exp_partial_solve_wit_3_aux.

Definition mpz_mul_2exp_partial_solve_wit_4_pure :=
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (cap >= 0) ”
) \/
(
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH7 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH12 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (r_pre = u_pre)) (PreH18 : (bits_pre >= 0)) (PreH19 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH20 : (same_sign z_eq size )) (PreH21 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
).

Definition mpz_mul_2exp_partial_solve_wit_4_pure_split_goal_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH7 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH12 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (r_pre = u_pre)) (PreH18 : (bits_pre >= 0)) (PreH19 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH20 : (same_sign z_eq size )) (PreH21 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_4_pure_split_goal_2 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (bits_pre <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH7 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH12 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (r_pre = u_pre)) (PreH18 : (bits_pre >= 0)) (PreH19 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH20 : (same_sign z_eq size )) (PreH21 : ((Zabs (size)) <= cap)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_4_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (cap >= 0) ”
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_mul_2exp_partial_solve_wit_4 := mpz_mul_2exp_partial_solve_wit_4_pure -> mpz_mul_2exp_partial_solve_wit_4_aux.

Definition mpz_mul_2exp_partial_solve_wit_5_pure :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l)) = un)) (PreH18 : (list_within_bound UINT_MOD l )) (PreH19 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH20 : ((last (l) (1)) >= 1)) (PreH21 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH22 : (u__mp_d = rp)) (PreH23 : (rp = u__mp_d)),
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un > 0) ”
  &&  “ (limbs >= 0) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
.

Definition mpz_mul_2exp_partial_solve_wit_5_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l)) = un)) (PreH18 : (list_within_bound UINT_MOD l )) (PreH19 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH20 : ((last (l) (1)) >= 1)) (PreH21 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH22 : (u__mp_d = rp)) (PreH23 : (rp = u__mp_d)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un > 0) ”
  &&  “ (limbs >= 0) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_5 := mpz_mul_2exp_partial_solve_wit_5_pure -> mpz_mul_2exp_partial_solve_wit_5_aux.

Definition mpz_mul_2exp_partial_solve_wit_6 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp (rn - 1 ) (un + limbs ) rn )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_7_pure :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un >= 0) ”
  &&  “ (limbs >= 0) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
.

Definition mpz_mul_2exp_partial_solve_wit_7_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un >= 0) ”
  &&  “ (limbs >= 0) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift = 0) ”
  &&  “ (rn = (un + limbs )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_7 := mpz_mul_2exp_partial_solve_wit_7_pure -> mpz_mul_2exp_partial_solve_wit_7_aux.

Definition mpz_mul_2exp_partial_solve_wit_8_pure :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val <> 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ”
  &&  “ (limbs <= INT_MAX) ”
.

Definition mpz_mul_2exp_partial_solve_wit_8_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val <> 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ”
  &&  “ (limbs <= INT_MAX) ”
  &&  “ (cy_val <> 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_8 := mpz_mul_2exp_partial_solve_wit_8_pure -> mpz_mul_2exp_partial_solve_wit_8_aux.

Definition mpz_mul_2exp_partial_solve_wit_9_pure :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val = 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ”
  &&  “ (limbs <= INT_MAX) ”
.

Definition mpz_mul_2exp_partial_solve_wit_9_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val = 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)),
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ”
  &&  “ (limbs <= INT_MAX) ”
  &&  “ (cy_val = 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_9 := mpz_mul_2exp_partial_solve_wit_9_pure -> mpz_mul_2exp_partial_solve_wit_9_aux.

Definition mpz_mul_2exp_partial_solve_wit_10_pure :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ”
  &&  “ (limbs <= INT_MAX) ”
.

Definition mpz_mul_2exp_partial_solve_wit_10_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ”
  &&  “ (limbs <= INT_MAX) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift = 0) ”
  &&  “ (rn = (un + limbs )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_10 := mpz_mul_2exp_partial_solve_wit_10_pure -> mpz_mul_2exp_partial_solve_wit_10_aux.

Definition mpz_mul_2exp_partial_solve_wit_11 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size < 0) ”
  &&  “ ((Zlength (l)) = limbs) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  “ (cy_val <> 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_12 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size >= 0) ”
  &&  “ ((Zlength (l)) = limbs) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  “ (cy_val <> 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_13 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size < 0) ”
  &&  “ ((Zlength (l)) = limbs) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  “ (cy_val = 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_14 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size >= 0) ”
  &&  “ ((Zlength (l)) = limbs) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  “ (cy_val = 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift > 0) ”
  &&  “ (1 <= shift) ”
  &&  “ (shift < 32) ”
  &&  “ (rn = ((un + limbs ) + 1 )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l_in)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_in ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ”
  &&  “ ((last (l_in) (1)) >= 1) ”
  &&  “ ((Zlength (l_out)) = un) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_15 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (size < 0) ”
  &&  “ ((Zlength (l_2)) = limbs) ”
  &&  “ (list_within_bound UINT_MOD l_2 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_2)) = 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift = 0) ”
  &&  “ (rn = (un + limbs )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_16 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (bits_pre: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)),
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (size >= 0) ”
  &&  “ ((Zlength (l_2)) = limbs) ”
  &&  “ (list_within_bound UINT_MOD l_2 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_2)) = 0) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (bits_pre >= 0) ”
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ”
  &&  “ (same_sign z_eq size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (un = (Zabs (size))) ”
  &&  “ (un > 0) ”
  &&  “ (limbs = (bits_pre ÷ 32 )) ”
  &&  “ (limbs >= 0) ”
  &&  “ (shift = (bits_pre % ( 32 ) )) ”
  &&  “ (shift = 0) ”
  &&  “ (rn = (un + limbs )) ”
  &&  “ (rn <= INT_MAX) ”
  &&  “ ((un + limbs ) <= INT_MAX) ”
  &&  “ ((Zlength (l)) = un) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ”
  &&  “ (u__mp_d = rp) ”
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_copyd_safety_wit_1 : mpn_copyd_safety_wit_1.
Axiom proof_of_mpn_copyd_safety_wit_2_off_zero : mpn_copyd_safety_wit_2_off_zero.
Axiom proof_of_mpn_copyd_safety_wit_3_off_pos : mpn_copyd_safety_wit_3_off_pos.
Axiom proof_of_mpn_copyd_safety_wit_4_off_zero : mpn_copyd_safety_wit_4_off_zero.
Axiom proof_of_mpn_copyd_safety_wit_5_off_pos : mpn_copyd_safety_wit_5_off_pos.
Axiom proof_of_mpn_copyd_safety_wit_6_off_zero : mpn_copyd_safety_wit_6_off_zero.
Axiom proof_of_mpn_copyd_safety_wit_7_off_pos : mpn_copyd_safety_wit_7_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_1_off_zero : mpn_copyd_entail_wit_1_off_zero.
Axiom proof_of_mpn_copyd_entail_wit_2_off_pos : mpn_copyd_entail_wit_2_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_3_off_zero : mpn_copyd_entail_wit_3_off_zero.
Axiom proof_of_mpn_copyd_entail_wit_4_off_pos : mpn_copyd_entail_wit_4_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_5_off_pos : mpn_copyd_entail_wit_5_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_6_off_zero : mpn_copyd_entail_wit_6_off_zero.
Axiom proof_of_mpn_copyd_entail_wit_7_off_pos : mpn_copyd_entail_wit_7_off_pos.
Axiom proof_of_mpn_copyd_return_wit_1_off_zero : mpn_copyd_return_wit_1_off_zero.
Axiom proof_of_mpn_copyd_return_wit_2_off_pos : mpn_copyd_return_wit_2_off_pos.
Axiom proof_of_mpn_copyd_partial_solve_wit_1 : mpn_copyd_partial_solve_wit_1.
Axiom proof_of_mpn_copyd_partial_solve_wit_2_off_zero_pure : mpn_copyd_partial_solve_wit_2_off_zero_pure.
Axiom proof_of_mpn_copyd_partial_solve_wit_2_off_zero : mpn_copyd_partial_solve_wit_2_off_zero.
Axiom proof_of_mpn_copyd_partial_solve_wit_3_off_pos_pure : mpn_copyd_partial_solve_wit_3_off_pos_pure.
Axiom proof_of_mpn_copyd_partial_solve_wit_3_off_pos : mpn_copyd_partial_solve_wit_3_off_pos.
Axiom proof_of_mpn_copyd_partial_solve_wit_4_off_zero : mpn_copyd_partial_solve_wit_4_off_zero.
Axiom proof_of_mpn_copyd_partial_solve_wit_5_off_zero : mpn_copyd_partial_solve_wit_5_off_zero.
Axiom proof_of_mpn_copyd_partial_solve_wit_6_off_pos : mpn_copyd_partial_solve_wit_6_off_pos.
Axiom proof_of_mpn_copyd_partial_solve_wit_7_off_pos : mpn_copyd_partial_solve_wit_7_off_pos.
Axiom proof_of_mpn_copyd_which_implies_wit_1 : mpn_copyd_which_implies_wit_1.
Axiom proof_of_mpn_copyd_which_implies_wit_2 : mpn_copyd_which_implies_wit_2.
Axiom proof_of_mpn_copyd_which_implies_wit_3 : mpn_copyd_which_implies_wit_3.
Axiom proof_of_mpn_zero_safety_wit_1 : mpn_zero_safety_wit_1.
Axiom proof_of_mpn_zero_safety_wit_2 : mpn_zero_safety_wit_2.
Axiom proof_of_mpn_zero_safety_wit_3 : mpn_zero_safety_wit_3.
Axiom proof_of_mpn_zero_safety_wit_4 : mpn_zero_safety_wit_4.
Axiom proof_of_mpn_zero_entail_wit_1 : mpn_zero_entail_wit_1.
Axiom proof_of_mpn_zero_entail_wit_2 : mpn_zero_entail_wit_2.
Axiom proof_of_mpn_zero_return_wit_1 : mpn_zero_return_wit_1.
Axiom proof_of_mpn_zero_partial_solve_wit_1 : mpn_zero_partial_solve_wit_1.
Axiom proof_of_mpn_zero_partial_solve_wit_2_pure : mpn_zero_partial_solve_wit_2_pure.
Axiom proof_of_mpn_zero_partial_solve_wit_2 : mpn_zero_partial_solve_wit_2.
Axiom proof_of_mpn_zero_partial_solve_wit_3 : mpn_zero_partial_solve_wit_3.
Axiom proof_of_mpn_zero_which_implies_wit_1 : mpn_zero_which_implies_wit_1.
Axiom proof_of_mpn_zero_which_implies_wit_2 : mpn_zero_which_implies_wit_2.
Axiom proof_of_mpz_mul_2exp_safety_wit_1 : mpz_mul_2exp_safety_wit_1.
Axiom proof_of_mpz_mul_2exp_safety_wit_2 : mpz_mul_2exp_safety_wit_2.
Axiom proof_of_mpz_mul_2exp_safety_wit_3 : mpz_mul_2exp_safety_wit_3.
Axiom proof_of_mpz_mul_2exp_safety_wit_4 : mpz_mul_2exp_safety_wit_4.
Axiom proof_of_mpz_mul_2exp_safety_wit_5 : mpz_mul_2exp_safety_wit_5.
Axiom proof_of_mpz_mul_2exp_safety_wit_6 : mpz_mul_2exp_safety_wit_6.
Axiom proof_of_mpz_mul_2exp_safety_wit_7 : mpz_mul_2exp_safety_wit_7.
Axiom proof_of_mpz_mul_2exp_safety_wit_8 : mpz_mul_2exp_safety_wit_8.
Axiom proof_of_mpz_mul_2exp_safety_wit_9 : mpz_mul_2exp_safety_wit_9.
Axiom proof_of_mpz_mul_2exp_safety_wit_10 : mpz_mul_2exp_safety_wit_10.
Axiom proof_of_mpz_mul_2exp_safety_wit_11 : mpz_mul_2exp_safety_wit_11.
Axiom proof_of_mpz_mul_2exp_safety_wit_12 : mpz_mul_2exp_safety_wit_12.
Axiom proof_of_mpz_mul_2exp_safety_wit_13 : mpz_mul_2exp_safety_wit_13.
Axiom proof_of_mpz_mul_2exp_safety_wit_14 : mpz_mul_2exp_safety_wit_14.
Axiom proof_of_mpz_mul_2exp_safety_wit_15 : mpz_mul_2exp_safety_wit_15.
Axiom proof_of_mpz_mul_2exp_safety_wit_16 : mpz_mul_2exp_safety_wit_16.
Axiom proof_of_mpz_mul_2exp_safety_wit_17 : mpz_mul_2exp_safety_wit_17.
Axiom proof_of_mpz_mul_2exp_safety_wit_18 : mpz_mul_2exp_safety_wit_18.
Axiom proof_of_mpz_mul_2exp_safety_wit_19 : mpz_mul_2exp_safety_wit_19.
Axiom proof_of_mpz_mul_2exp_safety_wit_20 : mpz_mul_2exp_safety_wit_20.
Axiom proof_of_mpz_mul_2exp_safety_wit_21 : mpz_mul_2exp_safety_wit_21.
Axiom proof_of_mpz_mul_2exp_safety_wit_22 : mpz_mul_2exp_safety_wit_22.
Axiom proof_of_mpz_mul_2exp_safety_wit_23 : mpz_mul_2exp_safety_wit_23.
Axiom proof_of_mpz_mul_2exp_safety_wit_24 : mpz_mul_2exp_safety_wit_24.
Axiom proof_of_mpz_mul_2exp_safety_wit_25 : mpz_mul_2exp_safety_wit_25.
Axiom proof_of_mpz_mul_2exp_entail_wit_1 : mpz_mul_2exp_entail_wit_1.
Axiom proof_of_mpz_mul_2exp_entail_wit_2 : mpz_mul_2exp_entail_wit_2.
Axiom proof_of_mpz_mul_2exp_entail_wit_3 : mpz_mul_2exp_entail_wit_3.
Axiom proof_of_mpz_mul_2exp_entail_wit_4 : mpz_mul_2exp_entail_wit_4.
Axiom proof_of_mpz_mul_2exp_entail_wit_5 : mpz_mul_2exp_entail_wit_5.
Axiom proof_of_mpz_mul_2exp_return_wit_1 : mpz_mul_2exp_return_wit_1.
Axiom proof_of_mpz_mul_2exp_return_wit_2 : mpz_mul_2exp_return_wit_2.
Axiom proof_of_mpz_mul_2exp_return_wit_3 : mpz_mul_2exp_return_wit_3.
Axiom proof_of_mpz_mul_2exp_return_wit_4 : mpz_mul_2exp_return_wit_4.
Axiom proof_of_mpz_mul_2exp_return_wit_5 : mpz_mul_2exp_return_wit_5.
Axiom proof_of_mpz_mul_2exp_return_wit_6 : mpz_mul_2exp_return_wit_6.
Axiom proof_of_mpz_mul_2exp_return_wit_7 : mpz_mul_2exp_return_wit_7.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_1_pure : mpz_mul_2exp_partial_solve_wit_1_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_1 : mpz_mul_2exp_partial_solve_wit_1.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_2 : mpz_mul_2exp_partial_solve_wit_2.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_3_pure : mpz_mul_2exp_partial_solve_wit_3_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_3 : mpz_mul_2exp_partial_solve_wit_3.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_4_pure : mpz_mul_2exp_partial_solve_wit_4_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_4 : mpz_mul_2exp_partial_solve_wit_4.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_5_pure : mpz_mul_2exp_partial_solve_wit_5_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_5 : mpz_mul_2exp_partial_solve_wit_5.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_6 : mpz_mul_2exp_partial_solve_wit_6.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_7_pure : mpz_mul_2exp_partial_solve_wit_7_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_7 : mpz_mul_2exp_partial_solve_wit_7.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_8_pure : mpz_mul_2exp_partial_solve_wit_8_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_8 : mpz_mul_2exp_partial_solve_wit_8.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_9_pure : mpz_mul_2exp_partial_solve_wit_9_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_9 : mpz_mul_2exp_partial_solve_wit_9.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_10_pure : mpz_mul_2exp_partial_solve_wit_10_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_10 : mpz_mul_2exp_partial_solve_wit_10.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_11 : mpz_mul_2exp_partial_solve_wit_11.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_12 : mpz_mul_2exp_partial_solve_wit_12.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_13 : mpz_mul_2exp_partial_solve_wit_13.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_14 : mpz_mul_2exp_partial_solve_wit_14.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_15 : mpz_mul_2exp_partial_solve_wit_15.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_16 : mpz_mul_2exp_partial_solve_wit_16.

End VC_Correct.
