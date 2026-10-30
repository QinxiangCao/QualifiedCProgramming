From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_normalized_size -----*)

Definition mpn_normalized_size_safety_wit_1_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (n <= n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH6 : (list_within_bound UINT_MOD lp )) (PreH7 : ((Zlength (lp)) = n_pre)) (PreH8 : (0 <= n_pre)),
  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_2_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : (normalized_size_read0_guard n l )) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre > 0)),
  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n_pre l )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_3_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_safety_wit_4_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n_pre l )
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_safety_wit_5_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n_pre l )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_normalized_size_safety_wit_6_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_normalized_size_safety_wit_7_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_8_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_9_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_safety_wit_10_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_entail_wit_1_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH2 : (list_within_bound UINT_MOD lp )) (PreH3 : ((Zlength (lp)) = n_pre)) (PreH4 : (0 <= n_pre)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre lp )
|--
  “ (n_pre <= INT_MAX) ”
  &&  “ ((list_to_Z (UINT_MOD) (lp)) = val_plain) ”
  &&  “ (list_within_bound UINT_MOD lp ) ”
  &&  “ ((Zlength (lp)) = n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre lp )
.

Definition mpn_normalized_size_entail_wit_2_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (PreH1 : (n_pre > 0)),
  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (mpd_store_Z UINT_MOD xp_pre val_read0 n_pre )
|--
  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre > 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (mpd_store_Z UINT_MOD xp_pre val_read0 n_pre )
.

Definition mpn_normalized_size_entail_wit_3_plain :=
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH3 : (list_within_bound UINT_MOD lp )) (PreH4 : ((Zlength (lp)) = n_pre)) (PreH5 : (0 <= n_pre)),
  (UIntArray.full xp_pre n_pre lp )
|--
  “ (n_pre >= 0) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (lp)))) = val_plain) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ ((list_to_Z (UINT_MOD) (lp)) = val_plain) ”
  &&  “ (list_within_bound UINT_MOD lp ) ”
  &&  “ ((Zlength (lp)) = n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n_pre (sublist (0) (n_pre) (lp)) )
  **  (UIntArray.undef_seg xp_pre n_pre n_pre )
) \/
(
forall (val_plain: Z) (n_pre: Z) (lp: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH3 : (list_within_bound UINT_MOD lp )) (PreH4 : ((Zlength (lp)) = n_pre)) (PreH5 : (0 <= n_pre)),
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (lp)))) = val_plain) ”
  &&  “ (lp = (sublist (0) (n_pre) (lp))) ”
  &&  emp
).

Definition mpn_normalized_size_entail_wit_3_plain_split_goal_1 :=
forall (val_plain: Z) (n_pre: Z) (lp: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH3 : (list_within_bound UINT_MOD lp )) (PreH4 : ((Zlength (lp)) = n_pre)) (PreH5 : (0 <= n_pre)),
  ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (lp)))) = val_plain)
.

Definition mpn_normalized_size_entail_wit_3_plain_split_goal_2 :=
forall (val_plain: Z) (n_pre: Z) (lp: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH3 : (list_within_bound UINT_MOD lp )) (PreH4 : ((Zlength (lp)) = n_pre)) (PreH5 : (0 <= n_pre)),
  (lp = (sublist (0) (n_pre) (lp)))
.

Definition mpn_normalized_size_entail_wit_4_read0 :=
(
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ (normalized_size_read0_guard n_pre l ) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre > 0) ”
  &&  (UIntArray.full xp_pre n_pre l )
) \/
(
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre > 0)),
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val_read0) ”
  &&  “ (normalized_size_read0_guard n_pre l ) ”
  &&  emp
).

Definition mpn_normalized_size_entail_wit_4_read0_split_goal_1 :=
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre > 0)),
  ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val_read0)
.

Definition mpn_normalized_size_entail_wit_4_read0_split_goal_2 :=
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre > 0)),
  (normalized_size_read0_guard n_pre l )
.

Definition mpn_normalized_size_entail_wit_5_plain :=
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((n - 1 ) >= 0) ”
  &&  “ ((n - 1 ) <= n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (lp)))) = val_plain) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ ((list_to_Z (UINT_MOD) (lp)) = val_plain) ”
  &&  “ (list_within_bound UINT_MOD lp ) ”
  &&  “ ((Zlength (lp)) = n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (lp)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
) \/
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (lp)))) = val_plain) ”
  &&  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (lp)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
).

Definition mpn_normalized_size_entail_wit_5_plain_split_goal_1 :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (lp)))) = val_plain) ”
.

Definition mpn_normalized_size_entail_wit_5_plain_split_goal_spatial :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (lp)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
.

Definition mpn_normalized_size_entail_wit_6_read0 :=
(
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre > 0) ”
  &&  “ ((n - 1 ) >= 0) ”
  &&  “ ((n - 1 ) <= n_pre) ”
  &&  “ (normalized_size_read0_guard (n - 1 ) l ) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre > 0) ”
  &&  (UIntArray.full xp_pre n_pre l )
) \/
(
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val_read0) ”
  &&  “ (normalized_size_read0_guard (n - 1 ) l ) ”
  &&  emp
).

Definition mpn_normalized_size_entail_wit_6_read0_split_goal_1 :=
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val_read0)
.

Definition mpn_normalized_size_entail_wit_6_read0_split_goal_2 :=
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  (normalized_size_read0_guard (n - 1 ) l )
.

Definition mpn_normalized_size_entail_wit_7_1_read0 :=
(
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre > 0) ”
  &&  “ (n >= 0) ”
  &&  “ (n <= n_pre) ”
  &&  “ (normalized_size_read0_guard n l ) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((last ((sublist (0) (n) (l))) (1)) >= 1) ”
  &&  (UIntArray.full xp_pre n_pre l )
) \/
(
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  TT && emp 
|--
  “ ((last ((sublist (0) (n) (l))) (1)) >= 1) ”
  &&  emp
).

Definition mpn_normalized_size_entail_wit_7_1_read0_split_goal_1 :=
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  ((last ((sublist (0) (n) (l))) (1)) >= 1)
.

Definition mpn_normalized_size_entail_wit_7_2_read0 :=
(
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre > 0) ”
  &&  “ (n >= 0) ”
  &&  “ (n <= n_pre) ”
  &&  “ (normalized_size_read0_guard n l ) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((last ((sublist (0) (n) (l))) (1)) >= 1) ”
  &&  (UIntArray.full xp_pre n_pre l )
) \/
(
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  TT && emp 
|--
  “ ((last ((sublist (0) (n) (l))) (1)) >= 1) ”
  &&  emp
).

Definition mpn_normalized_size_entail_wit_7_2_read0_split_goal_1 :=
forall (val_read0: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) l 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n_pre > 0)) (PreH4 : (n >= 0)) (PreH5 : (n <= n_pre)) (PreH6 : (normalized_size_read0_guard n l )) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre > 0)),
  ((last ((sublist (0) (n) (l))) (1)) >= 1)
.

Definition mpn_normalized_size_return_wit_1_read0 :=
(
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : (normalized_size_read0_guard n l )) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((last ((sublist (0) (n) (l))) (1)) >= 1)),
  (UIntArray.full xp_pre n_pre l )
|--
  “ (0 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact_read0 xp_pre val_read0 n )
  **  (UIntArray.undef_seg xp_pre (Zmax (n) (1)) n_pre )
) \/
(
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : (normalized_size_read0_guard n l )) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((last ((sublist (0) (n) (l))) (1)) >= 1)),
  (UIntArray.full xp_pre n_pre l )
|--
  (mpd_store_Z_compact_read0 xp_pre val_read0 n )
  **  (UIntArray.undef_seg xp_pre (Zmax (n) (1)) n_pre )
).

Definition mpn_normalized_size_return_wit_1_read0_split_goal_spatial :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : (normalized_size_read0_guard n l )) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((last ((sublist (0) (n) (l))) (1)) >= 1)),
  (UIntArray.full xp_pre n_pre l )
|--
  (mpd_store_Z_compact_read0 xp_pre val_read0 n )
  **  (UIntArray.undef_seg xp_pre (Zmax (n) (1)) n_pre )
.

Definition mpn_normalized_size_return_wit_2_plain :=
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (0 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val_plain n )
  **  (UIntArray.undef_seg xp_pre n n_pre )
) \/
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val_plain n )
).

Definition mpn_normalized_size_return_wit_2_plain_split_goal_spatial :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val_plain n )
.

Definition mpn_normalized_size_return_wit_3_plain :=
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (0 <= n) ”
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val_plain n )
  **  (UIntArray.undef_seg xp_pre n n_pre )
) \/
(
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val_plain n )
).

Definition mpn_normalized_size_return_wit_3_plain_split_goal_spatial :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (lp)) 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH8 : (list_within_bound UINT_MOD lp )) (PreH9 : ((Zlength (lp)) = n_pre)) (PreH10 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val_plain n )
.

Definition mpn_normalized_size_partial_solve_wit_1_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)),
  (mpd_store_Z UINT_MOD xp_pre val_plain n_pre )
|--
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z UINT_MOD xp_pre val_plain n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_2_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre > 0)),
  (mpd_store_Z UINT_MOD xp_pre val_read0 n_pre )
|--
  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre > 0) ”
  &&  (mpd_store_Z UINT_MOD xp_pre val_read0 n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_3_read0 :=
forall (val_read0: Z) (xp_pre: Z) (n_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n_pre > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : (normalized_size_read0_guard n l )) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l)) = val_read0)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre > 0)),
  (UIntArray.full xp_pre n_pre l )
|--
  “ (n > 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n >= 0) ”
  &&  “ (n <= n_pre) ”
  &&  “ (normalized_size_read0_guard n l ) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre > 0) ”
  &&  (((xp_pre + ((n - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n - 1 ) l 0))
  **  (UIntArray.missing_i xp_pre (n - 1 ) 0 n_pre l )
.

Definition mpn_normalized_size_partial_solve_wit_4_plain :=
forall (val_plain: Z) (xp_pre: Z) (n_pre: Z) (lp: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (lp)) = val_plain)) (PreH7 : (list_within_bound UINT_MOD lp )) (PreH8 : ((Zlength (lp)) = n_pre)) (PreH9 : (0 <= n_pre)),
  (UIntArray.full xp_pre n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (n > 0) ”
  &&  “ (n >= 0) ”
  &&  “ (n <= n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (lp)))) = val_plain) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ ((list_to_Z (UINT_MOD) (lp)) = val_plain) ”
  &&  “ (list_within_bound UINT_MOD lp ) ”
  &&  “ ((Zlength (lp)) = n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  (((xp_pre + ((n - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n - 1 ) (sublist (0) (n) (lp)) 0))
  **  (UIntArray.missing_i xp_pre (n - 1 ) 0 n (sublist (0) (n) (lp)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
.

Definition mpn_normalized_size_which_implies_wit_1 :=
(
forall (val_plain: Z) (n: Z) (xp: Z),
  (mpd_store_Z UINT_MOD xp val_plain n )
|--
  EX (lp: (@list Z)),
  “ ((list_to_Z (UINT_MOD) (lp)) = val_plain) ”
  &&  “ (list_within_bound UINT_MOD lp ) ”
  &&  “ ((Zlength (lp)) = n) ”
  &&  (UIntArray.full xp n lp )
) \/
(
forall (val_plain: Z) (n: Z) (xp: Z),
  (mpd_store_Z UINT_MOD xp val_plain n )
|--
  EX (lp: (@list Z)),
  “ ((list_to_Z (UINT_MOD) (lp)) = val_plain) ”
  &&  “ (list_within_bound UINT_MOD lp ) ”
  &&  “ ((Zlength (lp)) = n) ”
  &&  (UIntArray.full xp n lp )
).

Definition mpn_normalized_size_which_implies_wit_2 :=
(
forall (val_read0: Z) (n: Z) (xp: Z),
  (mpd_store_Z UINT_MOD xp val_read0 n )
|--
  EX (l: (@list Z)),
  “ ((list_to_Z (UINT_MOD) (l)) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n) ”
  &&  (UIntArray.full xp n l )
) \/
(
forall (val_read0: Z) (n: Z) (xp: Z),
  (mpd_store_Z UINT_MOD xp val_read0 n )
|--
  EX (l: (@list Z)),
  “ ((list_to_Z (UINT_MOD) (l)) = val_read0) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((Zlength (l)) = n) ”
  &&  (UIntArray.full xp n l )
).

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_normalized_size_safety_wit_1_plain : mpn_normalized_size_safety_wit_1_plain.
Axiom proof_of_mpn_normalized_size_safety_wit_2_read0 : mpn_normalized_size_safety_wit_2_read0.
Axiom proof_of_mpn_normalized_size_safety_wit_3_plain : mpn_normalized_size_safety_wit_3_plain.
Axiom proof_of_mpn_normalized_size_safety_wit_4_read0 : mpn_normalized_size_safety_wit_4_read0.
Axiom proof_of_mpn_normalized_size_safety_wit_5_read0 : mpn_normalized_size_safety_wit_5_read0.
Axiom proof_of_mpn_normalized_size_safety_wit_6_plain : mpn_normalized_size_safety_wit_6_plain.
Axiom proof_of_mpn_normalized_size_safety_wit_7_read0 : mpn_normalized_size_safety_wit_7_read0.
Axiom proof_of_mpn_normalized_size_safety_wit_8_plain : mpn_normalized_size_safety_wit_8_plain.
Axiom proof_of_mpn_normalized_size_safety_wit_9_plain : mpn_normalized_size_safety_wit_9_plain.
Axiom proof_of_mpn_normalized_size_safety_wit_10_read0 : mpn_normalized_size_safety_wit_10_read0.
Axiom proof_of_mpn_normalized_size_entail_wit_1_plain : mpn_normalized_size_entail_wit_1_plain.
Axiom proof_of_mpn_normalized_size_entail_wit_2_read0 : mpn_normalized_size_entail_wit_2_read0.
Axiom proof_of_mpn_normalized_size_entail_wit_3_plain : mpn_normalized_size_entail_wit_3_plain.
Axiom proof_of_mpn_normalized_size_entail_wit_4_read0 : mpn_normalized_size_entail_wit_4_read0.
Axiom proof_of_mpn_normalized_size_entail_wit_5_plain : mpn_normalized_size_entail_wit_5_plain.
Axiom proof_of_mpn_normalized_size_entail_wit_6_read0 : mpn_normalized_size_entail_wit_6_read0.
Axiom proof_of_mpn_normalized_size_entail_wit_7_1_read0 : mpn_normalized_size_entail_wit_7_1_read0.
Axiom proof_of_mpn_normalized_size_entail_wit_7_2_read0 : mpn_normalized_size_entail_wit_7_2_read0.
Axiom proof_of_mpn_normalized_size_return_wit_1_read0 : mpn_normalized_size_return_wit_1_read0.
Axiom proof_of_mpn_normalized_size_return_wit_2_plain : mpn_normalized_size_return_wit_2_plain.
Axiom proof_of_mpn_normalized_size_return_wit_3_plain : mpn_normalized_size_return_wit_3_plain.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_1_plain : mpn_normalized_size_partial_solve_wit_1_plain.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_2_read0 : mpn_normalized_size_partial_solve_wit_2_read0.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_3_read0 : mpn_normalized_size_partial_solve_wit_3_read0.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_4_plain : mpn_normalized_size_partial_solve_wit_4_plain.
Axiom proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Axiom proof_of_mpn_normalized_size_which_implies_wit_2 : mpn_normalized_size_which_implies_wit_2.

End VC_Correct.
