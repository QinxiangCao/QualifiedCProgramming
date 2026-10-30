From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_lshift -----*)

Definition mpn_lshift_safety_wit_1_shifted :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((False \/ (True /\ (off_shifted = 0))) \/ (True /\ (off_shifted > 0))) ”
.

Definition mpn_lshift_safety_wit_2_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_3_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_4_off_zero :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_5_off_pos :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_6_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_7_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_8_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_9_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_10_off_zero :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_11_off_zero :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_12_off_pos :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_13_off_pos :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_14_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((32 - cnt_pre ) <= 31) ”
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_15_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ”
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_16_off_zero :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ”
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_17_off_pos :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ”
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_18_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_19_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_20_off_zero :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_21_off_pos :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_22_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) (PreH17 : (tnc = (32 - cnt_pre ))) (PreH18 : (1 <= cnt_pre)) (PreH19 : (cnt_pre < 32)) (PreH20 : (0 <= low_limb)) (PreH21 : (low_limb <= UINT_MAX)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH27 : (l_done = (@nil Z))) (PreH28 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH29 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH34 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_23_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) (PreH17 : (tnc = (32 - cnt_pre ))) (PreH18 : (1 <= cnt_pre)) (PreH19 : (cnt_pre < 32)) (PreH20 : (0 <= low_limb)) (PreH21 : (low_limb <= UINT_MAX)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : ((Zlength (l_up_inplace)) = n_pre)) (PreH27 : (l_done = (@nil Z))) (PreH28 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH29 : (list_within_bound UINT_MOD l_up_inplace )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH34 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_24_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < n_pre)) (PreH8 : ((Zlength (l_up_shifted)) = n_pre)) (PreH9 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH10 : (list_within_bound UINT_MOD l_up_shifted )) (PreH11 : (list_within_bound UINT_MOD l_done_2 )) (PreH12 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (off_shifted = 0)) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (i = (n_pre - 1 ))) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : ((Zlength (l_up_shifted)) = n_pre)) (PreH25 : (l_done = (@nil Z))) (PreH26 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH27 : (list_within_bound UINT_MOD l_up_shifted )) (PreH28 : (list_within_bound UINT_MOD l_done )) (PreH29 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH30 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH31 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH32 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_25_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted > 0)) (PreH18 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH19 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH20 : (tnc = (32 - cnt_pre ))) (PreH21 : (1 <= cnt_pre)) (PreH22 : (cnt_pre < 32)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : ((Zlength (l_up_shifted)) = n_pre)) (PreH27 : (l_done = (@nil Z))) (PreH28 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH29 : (list_within_bound UINT_MOD l_up_shifted )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_26_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i_2: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_27_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_28_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i_2: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_2 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_29_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_30_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i_2: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done = (@nil Z))) (PreH27 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_31_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done = (@nil Z))) (PreH27 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_32_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i_2: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH34 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_33_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i = (n_pre - 1 ))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH33 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH34 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_34_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_35_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_36_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_37_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_38_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_39_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_40_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_41_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_42_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (tnc <= 31) ”
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_43_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc <= 31) ”
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_44_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc <= 31) ”
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_45_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc <= 31) ”
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_46_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb (Z.shiftr low_limb tnc)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_47_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (replace_Znth (((i + 1 ) - (i + 1 ) )) ((Z.lor high_limb (Z.shiftr low_limb tnc))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_48_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH9 : (0 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (replace_Znth (((i + 1 ) - (i + 1 ) )) ((Z.lor high_limb (Z.shiftr low_limb tnc))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_49_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb (Z.shiftr low_limb tnc)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_50_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (0 = 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (i = 0)) (PreH8 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH13 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH14 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_51_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH15 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_52_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (off_shifted = 0)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (i = 0)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_53_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (0 = 0)) (PreH3 : (off_shifted > 0)) (PreH4 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (tnc = (32 - cnt_pre ))) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (0 <= low_limb)) (PreH10 : (low_limb <= UINT_MAX)) (PreH11 : (i = 0)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_entail_wit_1_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (rp_pre <> up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_entail_wit_2_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (UIntArray.full up_pre n_pre l_up_inplace )
.

Definition mpn_lshift_entail_wit_3_nonalias :=
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.undef_seg rp_pre 0 n_pre )
  **  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done: (@list Z)),
  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_nonalias 0)) ”
  &&  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) <= UINT_MAX) ”
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) = (Znth ((n_pre - 1 )) (l_up_nonalias) (0))) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((n_pre - 1 ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) <= UINT_MAX) ”
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_nonalias 0)) ”
  &&  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
).

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_1 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_2 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_3 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_4 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_5 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_6 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) <= UINT_MAX) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_7 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ (0 <= (Znth (n_pre - 1 ) l_up_nonalias 0)) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_spatial :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
.

Definition mpn_lshift_entail_wit_4_inplace :=
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  EX (l_done: (@list Z)),
  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_inplace 0)) ”
  &&  “ ((Znth (n_pre - 1 ) l_up_inplace 0) <= UINT_MAX) ”
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  “ ((Znth (n_pre - 1 ) l_up_inplace 0) = (Znth ((n_pre - 1 )) (l_up_inplace) (0))) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ ((Znth (n_pre - 1 ) l_up_inplace 0) <= UINT_MAX) ”
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_inplace 0)) ”
  &&  “ ((sublist (0) (n_pre) (l_up_inplace)) = (app ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace))) ((@nil Z)))) ”
  &&  “ ((Zlength ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace)))) = (((n_pre - 1 ) + 1 ) - 0 )) ”
  &&  emp
).

Definition mpn_lshift_entail_wit_4_inplace_split_goal_1 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_2 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_3 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_4 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_5 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_6 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Znth (n_pre - 1 ) l_up_inplace 0) <= UINT_MAX) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_7 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ (0 <= (Znth (n_pre - 1 ) l_up_inplace 0)) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_8 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((sublist (0) (n_pre) (l_up_inplace)) = (app ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace))) ((@nil Z)))) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_9 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Zlength ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace)))) = (((n_pre - 1 ) + 1 ) - 0 )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_spatial :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  TT && emp 
.

Definition mpn_lshift_entail_wit_5_off_zero :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
).

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_1 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_2 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_3 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_4 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_5 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_6 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_7 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ (rp_pre = up_pre) ”
.

Definition mpn_lshift_entail_wit_5_off_zero_split_goal_spatial :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
.

Definition mpn_lshift_entail_wit_6_off_pos :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre ((n_pre - 1 ) + 1 ) ((off_shifted + (n_pre - 1 ) ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
).

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_1 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_2 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_3 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_4 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
.

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_5 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_6 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_6_off_pos_split_goal_spatial :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
.

Definition mpn_lshift_entail_wit_7_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : (l_done = (@nil Z))) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (rp_pre <> up_pre)),
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done_2: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_entail_wit_8_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : (l_done = (@nil Z))) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_inplace )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done )
|--
  EX (l_done_2: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_entail_wit_9_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : (l_done = (@nil Z))) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done )
|--
  EX (l_done_2: (@list Z)),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_entail_wit_10_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (i = (n_pre - 1 ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : (l_done = (@nil Z))) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done )
|--
  EX (l_done_2: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_entail_wit_11_nonalias_inv :=
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth (i - 1 ) l_up_nonalias 0)) ”
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) <= UINT_MAX) ”
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) = (Znth ((i - 1 )) (l_up_nonalias) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((i - 1 ) + 2 ) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth (i - 1 ) l_up_nonalias 0)) ”
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) <= UINT_MAX) ”
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) = (Znth ((i - 1 )) (l_up_nonalias) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_12_inplace_inv :=
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0)) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) <= UINT_MAX) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) = (Znth ((i - 1 )) (l_up_inplace) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre ((i - 1 ) + 2 ) n_pre l_done )
) \/
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0)) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) <= UINT_MAX) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) = (Znth ((i - 1 )) (l_up_inplace) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_13_off_zero_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_14_off_pos_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre ((i - 1 ) + 2 ) ((off_shifted + (i - 1 ) ) + 2 ) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ (((i - 1 ) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_15_nonalias_inv :=
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done_2: (@list Z)) (high_limb: Z) (retval: Z) (l_done: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z),
  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb_2) ”
  &&  “ (low_limb_2 <= UINT_MAX) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) <= UINT_MAX)) (PreH2 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) >= 0)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb_2)) (PreH7 : (low_limb_2 <= UINT_MAX)) (PreH8 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH9 : (0 <= i_2)) (PreH10 : ((i_2 + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH12 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH14 : (list_within_bound UINT_MOD l_done_3 )) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (rp_pre <> up_pre)),
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)),
  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb_2) ”
  &&  “ (low_limb_2 <= UINT_MAX) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (Znth ((n_pre - 1 )) (l_up_nonalias) (0))) ”
  &&  “ ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) <= UINT_MAX) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
).

Definition mpn_lshift_entail_wit_16_inplace_inv :=
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre (i_2 + 1 ) (i_2 + 2 ) (replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)) (high_limb: Z) (retval: Z) (l_done: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z),
  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb_2) ”
  &&  “ (low_limb_2 <= UINT_MAX) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_inplace) (0))) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
) \/
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  TT && emp 
|--
  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) <= UINT_MAX) ”
  &&  “ (0 <= (Znth ((n_pre - 1 )) (l_up_inplace) (0))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits ((low_limb_2 * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (list_within_bound UINT_MOD (app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)) ) ”
  &&  “ ((Zlength ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) = (n_pre - (i_2 + 1 ) )) ”
  &&  emp
).

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_1 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_2 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_3 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) ))
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_4 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) <= UINT_MAX)
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_5 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  (0 <= (Znth ((n_pre - 1 )) (l_up_inplace) (0)))
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_6 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_7 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits ((low_limb_2 * (Z.pow (2) (cnt_pre)) )) (32)))
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_8 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  (list_within_bound UINT_MOD (app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)) )
.

Definition mpn_lshift_entail_wit_16_inplace_inv_split_goal_9 :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((Zlength ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) = (n_pre - (i_2 + 1 ) ))
.

Definition mpn_lshift_entail_wit_17_off_zero_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb_2)) (PreH7 : (low_limb_2 <= UINT_MAX)) (PreH8 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH9 : (0 <= i_2)) (PreH10 : ((i_2 + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done_3 )) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre (i_2 + 1 ) (i_2 + 2 ) (replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_shifted)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb_2)) (PreH7 : (low_limb_2 <= UINT_MAX)) (PreH8 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH9 : (0 <= i_2)) (PreH10 : ((i_2 + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done_3 )) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre (i_2 + 1 ) (i_2 + 2 ) (replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)),
  “ (up_pre = rp_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
).

Definition mpn_lshift_entail_wit_18_off_pos_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb_2)) (PreH9 : (low_limb_2 <= UINT_MAX)) (PreH10 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH11 : (0 <= i_2)) (PreH12 : ((i_2 + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done_3 )) (PreH17 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH18 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.undef_seg up_pre (i_2 + 2 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg up_pre 0 (i_2 + 2 ) (sublist (0) ((i_2 + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) <= UINT_MAX)) (PreH2 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) >= 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (off_shifted > 0)) (PreH5 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (tnc_2 = (32 - cnt_pre ))) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (0 <= low_limb_2)) (PreH11 : (low_limb_2 <= UINT_MAX)) (PreH12 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH13 : (0 <= i_2)) (PreH14 : ((i_2 + 1 ) < n_pre)) (PreH15 : ((Zlength (l_up_shifted)) = n_pre)) (PreH16 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH17 : (list_within_bound UINT_MOD l_up_shifted )) (PreH18 : (list_within_bound UINT_MOD l_done_3 )) (PreH19 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH20 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH21 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.undef_seg up_pre (i_2 + 2 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg up_pre 0 (i_2 + 2 ) (sublist (0) ((i_2 + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
).

Definition mpn_lshift_entail_wit_19_nonalias_inv :=
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.seg rp_pre 1 n_pre l_done )
).

Definition mpn_lshift_entail_wit_20_inplace_inv :=
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
) \/
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
).

Definition mpn_lshift_entail_wit_21_off_zero_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
).

Definition mpn_lshift_entail_wit_22_off_pos_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)),
  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
).

Definition mpn_lshift_return_wit_1_nonalias_inv :=
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre <> up_pre)),
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (high_limb <= UINT_MAX)) (PreH2 : (high_limb >= 0)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH15 : (rp_pre <> up_pre)),
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
).

Definition mpn_lshift_return_wit_2_inplace_inv :=
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)),
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_inplace)))) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
) \/
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)),
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_inplace)))) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
).

Definition mpn_lshift_return_wit_3_off_zero_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
).

Definition mpn_lshift_return_wit_4_off_pos_inv :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (i = 0)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (high_limb <= UINT_MAX)) (PreH2 : (high_limb >= 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (off_shifted > 0)) (PreH5 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (tnc = (32 - cnt_pre ))) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (0 <= low_limb)) (PreH11 : (low_limb <= UINT_MAX)) (PreH12 : (i = 0)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
).

Definition mpn_lshift_partial_solve_wit_1_shifted :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.full up_pre n_pre l_up_shifted )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre > 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (UIntArray.full up_pre n_pre l_up_shifted )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
.

Definition mpn_lshift_partial_solve_wit_2_nonalias :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (rp_pre <> up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre l_up_nonalias )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_lshift_partial_solve_wit_3_inplace :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre l_up_inplace )
.

Definition mpn_lshift_partial_solve_wit_4_off_zero :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre > 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (off_shifted = 0) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
.

Definition mpn_lshift_partial_solve_wit_5_off_pos :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)),
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre > 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
.

Definition mpn_lshift_partial_solve_wit_6_nonalias_pure :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  ((( &( "high_limb" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (rp_pre <> up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_6_nonalias_aux :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )),
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (rp_pre <> up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_6_nonalias := mpn_lshift_partial_solve_wit_6_nonalias_pure -> mpn_lshift_partial_solve_wit_6_nonalias_aux.

Definition mpn_lshift_partial_solve_wit_7_inplace_pure :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  ((( &( "high_limb" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_7_inplace_aux :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )),
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (UIntArray.full up_pre n_pre l_up_inplace )
.

Definition mpn_lshift_partial_solve_wit_7_inplace := mpn_lshift_partial_solve_wit_7_inplace_pure -> mpn_lshift_partial_solve_wit_7_inplace_aux.

Definition mpn_lshift_partial_solve_wit_8_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)),
  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (i_2 > 0) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb_2) ”
  &&  “ (low_limb_2 <= UINT_MAX) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (i_2 - 1 ) l_up_nonalias 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 n_pre l_up_nonalias )
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_9_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (i_2 > 0) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb_2) ”
  &&  “ (low_limb_2 <= UINT_MAX) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_inplace) (0))) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i_2 - 1 ) - 0 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_10_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done = (@nil Z))) (PreH27 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (i_2 > 0) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i_2 - 1 ) - 0 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_11_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i = (n_pre - 1 ))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH33 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH34 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (i_2 > 0) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc_2 = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ”
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ”
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ”
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (i = (n_pre - 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i_2 - 1 ) - 0 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_12_nonalias_inv_pure :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i + 1 ) >= 0) ”
  &&  “ ((i + 2 ) <= n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_12_nonalias_inv_aux :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i + 1 ) >= 0) ”
  &&  “ ((i + 2 ) <= n_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_12_nonalias_inv := mpn_lshift_partial_solve_wit_12_nonalias_inv_pure -> mpn_lshift_partial_solve_wit_12_nonalias_inv_aux.

Definition mpn_lshift_partial_solve_wit_13_inplace_inv_pure :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ ((i + 1 ) >= 0) ”
  &&  “ ((i + 2 ) <= n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_13_inplace_inv_aux :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ ((i + 1 ) >= 0) ”
  &&  “ ((i + 2 ) <= n_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_13_inplace_inv := mpn_lshift_partial_solve_wit_13_inplace_inv_pure -> mpn_lshift_partial_solve_wit_13_inplace_inv_aux.

Definition mpn_lshift_partial_solve_wit_14_off_zero_inv_pure :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH9 : (0 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_14_off_zero_inv_aux :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH9 : (0 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_14_off_zero_inv := mpn_lshift_partial_solve_wit_14_off_zero_inv_pure -> mpn_lshift_partial_solve_wit_14_off_zero_inv_aux.

Definition mpn_lshift_partial_solve_wit_15_off_pos_inv_pure :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_15_off_pos_inv_aux :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_15_off_pos_inv := mpn_lshift_partial_solve_wit_15_off_pos_inv_pure -> mpn_lshift_partial_solve_wit_15_off_pos_inv_aux.

Definition mpn_lshift_partial_solve_wit_16_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)),
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_17_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre (i + 1 ) (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_18_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre (i + 1 ) (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_19_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_20_nonalias_inv_pure :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre <> up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_20_nonalias_inv_aux :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre <> up_pre)),
  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 = 0) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_20_nonalias_inv := mpn_lshift_partial_solve_wit_20_nonalias_inv_pure -> mpn_lshift_partial_solve_wit_20_nonalias_inv_aux.

Definition mpn_lshift_partial_solve_wit_21_inplace_inv_pure :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_21_inplace_inv_aux :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ (0 = 0) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_21_inplace_inv := mpn_lshift_partial_solve_wit_21_inplace_inv_pure -> mpn_lshift_partial_solve_wit_21_inplace_inv_aux.

Definition mpn_lshift_partial_solve_wit_22_off_zero_inv_pure :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_22_off_zero_inv_aux :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ”
  &&  “ (0 = 0) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_22_off_zero_inv := mpn_lshift_partial_solve_wit_22_off_zero_inv_pure -> mpn_lshift_partial_solve_wit_22_off_zero_inv_aux.

Definition mpn_lshift_partial_solve_wit_23_off_pos_inv_pure :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (i = 0)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_23_off_pos_inv_aux :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (i = 0)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 = 0) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_23_off_pos_inv := mpn_lshift_partial_solve_wit_23_off_pos_inv_pure -> mpn_lshift_partial_solve_wit_23_off_pos_inv_aux.

Definition mpn_lshift_partial_solve_wit_24_nonalias_inv :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (0 = 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (i = 0)) (PreH8 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH13 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH14 : (rp_pre <> up_pre)),
  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre <> up_pre) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_25_inplace_inv :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH15 : (rp_pre = up_pre)),
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre 0 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_26_off_zero_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (off_shifted = 0)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (i = 0)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (off_shifted = 0) ”
  &&  “ (rp_pre = up_pre) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre 0 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_27_off_pos_inv :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (0 = 0)) (PreH3 : (off_shifted > 0)) (PreH4 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (tnc = (32 - cnt_pre ))) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (0 <= low_limb)) (PreH10 : (low_limb <= UINT_MAX)) (PreH11 : (i = 0)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))),
  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (0 <= low_limb) ”
  &&  “ (low_limb <= UINT_MAX) ”
  &&  “ (i = 0) ”
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ”
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ”
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_which_implies_wit_1 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (n: Z) (up: Z),
  (UIntArray.full up n l_up_shifted )
  **  (UIntArray.undef_seg up n (n + off_shifted ) )
|--
  (UIntArray.seg up 0 n (sublist (0) (n) (l_up_shifted)) )
  **  (UIntArray.undef_seg up n (n + off_shifted ) )
) \/
(
forall (l_up_shifted: (@list Z)) (n: Z) (up: Z),
  (UIntArray.full up n l_up_shifted )
|--
  (UIntArray.seg up 0 n (sublist (0) (n) (l_up_shifted)) )
).

Definition mpn_lshift_which_implies_wit_1_split_goal_spatial :=
forall (l_up_shifted: (@list Z)) (n: Z) (up: Z),
  (UIntArray.full up n l_up_shifted )
|--
  (UIntArray.seg up 0 n (sublist (0) (n) (l_up_shifted)) )
.

Definition mpn_lshift_which_implies_wit_2 :=
forall (l_up_nonalias: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)),
  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (rp_pre <> up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 n_pre )
  **  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_which_implies_wit_3 :=
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)),
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
) \/
(
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)),
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
).

Definition mpn_lshift_which_implies_wit_3_split_goal_spatial :=
forall (l_up_inplace: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)),
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
.

Definition mpn_lshift_which_implies_wit_4 :=
forall (rp_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= 0)) (PreH2 : ((i + 2 ) <= n_pre)),
  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
|--
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
.

Definition mpn_lshift_which_implies_wit_5 :=
(
forall (l_up_inplace: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)),
  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
|--
  “ (rp = up_pre) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
) \/
(
forall (l_up_inplace: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)),
  TT && emp 
|--
  “ ((sublist (0) ((i + 2 )) (l_up_inplace)) = (app ((sublist (0) ((i + 1 )) (l_up_inplace))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_inplace))))) ”
  &&  “ ((Zlength ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((i + 1 ) - 0 )) ”
  &&  emp
).

Definition mpn_lshift_which_implies_wit_5_split_goal_1 :=
forall (l_up_inplace: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)),
  ((sublist (0) ((i + 2 )) (l_up_inplace)) = (app ((sublist (0) ((i + 1 )) (l_up_inplace))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)))))
.

Definition mpn_lshift_which_implies_wit_5_split_goal_2 :=
forall (l_up_inplace: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)),
  ((Zlength ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((i + 1 ) - 0 ))
.

Definition mpn_lshift_which_implies_wit_6 :=
(
forall (l_up_shifted: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)),
  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
|--
  “ (rp = up_pre) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
) \/
(
forall (l_up_shifted: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)),
  TT && emp 
|--
  “ ((sublist (0) ((i + 2 )) (l_up_shifted)) = (app ((sublist (0) ((i + 1 )) (l_up_shifted))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_shifted))))) ”
  &&  “ ((Zlength ((sublist (0) ((i + 1 )) (l_up_shifted)))) = ((i + 1 ) - 0 )) ”
  &&  emp
).

Definition mpn_lshift_which_implies_wit_6_split_goal_1 :=
forall (l_up_shifted: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)),
  ((sublist (0) ((i + 2 )) (l_up_shifted)) = (app ((sublist (0) ((i + 1 )) (l_up_shifted))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)))))
.

Definition mpn_lshift_which_implies_wit_6_split_goal_2 :=
forall (l_up_shifted: (@list Z)) (up_pre: Z) (n_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)),
  ((Zlength ((sublist (0) ((i + 1 )) (l_up_shifted)))) = ((i + 1 ) - 0 ))
.

Definition mpn_lshift_which_implies_wit_7 :=
(
forall (off_shifted: Z) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : ((i + 1 ) < n_pre)),
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
) \/
(
forall (off_shifted: Z) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : ((i + 1 ) < n_pre)),
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
|--
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
).

Definition mpn_lshift_which_implies_wit_7_split_goal_spatial :=
forall (off_shifted: Z) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : ((i + 1 ) < n_pre)),
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
|--
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
.

Definition mpn_lshift_which_implies_wit_8 :=
forall (rp_pre: Z) (i: Z) (PreH1 : (i = 0)),
  (UIntArray.undef_seg rp_pre 0 1 )
|--
  “ (i = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 1 )
.

Definition mpn_lshift_which_implies_wit_9 :=
forall (l_up_inplace: (@list Z)) (up_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)),
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
|--
  “ (rp = up_pre) ”
  &&  “ (i = 0) ”
  &&  (UIntArray.seg rp 0 1 (sublist (0) (1) (l_up_inplace)) )
.

Definition mpn_lshift_which_implies_wit_10 :=
forall (l_up_shifted: (@list Z)) (up_pre: Z) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)),
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
|--
  “ (rp = up_pre) ”
  &&  “ (i = 0) ”
  &&  (UIntArray.seg rp 0 1 (sublist (0) (1) (l_up_shifted)) )
.

Definition mpn_lshift_which_implies_wit_11 :=
(
forall (off_shifted: Z) (rp_pre: Z) (up_pre: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (i = 0)),
  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (i = 0) ”
  &&  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
) \/
(
forall (off_shifted: Z) (rp_pre: Z) (up_pre: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (i = 0)),
  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
|--
  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
).

Definition mpn_lshift_which_implies_wit_11_split_goal_spatial :=
forall (off_shifted: Z) (rp_pre: Z) (up_pre: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (i = 0)),
  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
|--
  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_lshift_safety_wit_1_shifted : mpn_lshift_safety_wit_1_shifted.
Axiom proof_of_mpn_lshift_safety_wit_2_nonalias : mpn_lshift_safety_wit_2_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_3_inplace : mpn_lshift_safety_wit_3_inplace.
Axiom proof_of_mpn_lshift_safety_wit_4_off_zero : mpn_lshift_safety_wit_4_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_5_off_pos : mpn_lshift_safety_wit_5_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_6_nonalias : mpn_lshift_safety_wit_6_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_7_nonalias : mpn_lshift_safety_wit_7_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_8_inplace : mpn_lshift_safety_wit_8_inplace.
Axiom proof_of_mpn_lshift_safety_wit_9_inplace : mpn_lshift_safety_wit_9_inplace.
Axiom proof_of_mpn_lshift_safety_wit_10_off_zero : mpn_lshift_safety_wit_10_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_11_off_zero : mpn_lshift_safety_wit_11_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_12_off_pos : mpn_lshift_safety_wit_12_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_13_off_pos : mpn_lshift_safety_wit_13_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_14_nonalias : mpn_lshift_safety_wit_14_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_15_inplace : mpn_lshift_safety_wit_15_inplace.
Axiom proof_of_mpn_lshift_safety_wit_16_off_zero : mpn_lshift_safety_wit_16_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_17_off_pos : mpn_lshift_safety_wit_17_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_18_nonalias : mpn_lshift_safety_wit_18_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_19_inplace : mpn_lshift_safety_wit_19_inplace.
Axiom proof_of_mpn_lshift_safety_wit_20_off_zero : mpn_lshift_safety_wit_20_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_21_off_pos : mpn_lshift_safety_wit_21_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_22_nonalias_inv : mpn_lshift_safety_wit_22_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_23_inplace_inv : mpn_lshift_safety_wit_23_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_24_off_zero_inv : mpn_lshift_safety_wit_24_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_25_off_pos_inv : mpn_lshift_safety_wit_25_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_26_nonalias_inv : mpn_lshift_safety_wit_26_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_27_nonalias_inv : mpn_lshift_safety_wit_27_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_28_inplace_inv : mpn_lshift_safety_wit_28_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_29_inplace_inv : mpn_lshift_safety_wit_29_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_30_off_zero_inv : mpn_lshift_safety_wit_30_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_31_off_zero_inv : mpn_lshift_safety_wit_31_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_32_off_pos_inv : mpn_lshift_safety_wit_32_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_33_off_pos_inv : mpn_lshift_safety_wit_33_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_34_off_pos_inv : mpn_lshift_safety_wit_34_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_35_off_zero_inv : mpn_lshift_safety_wit_35_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_36_inplace_inv : mpn_lshift_safety_wit_36_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_37_nonalias_inv : mpn_lshift_safety_wit_37_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_38_nonalias_inv : mpn_lshift_safety_wit_38_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_39_inplace_inv : mpn_lshift_safety_wit_39_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_40_off_zero_inv : mpn_lshift_safety_wit_40_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_41_off_pos_inv : mpn_lshift_safety_wit_41_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_42_nonalias_inv : mpn_lshift_safety_wit_42_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_43_inplace_inv : mpn_lshift_safety_wit_43_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_44_off_zero_inv : mpn_lshift_safety_wit_44_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_45_off_pos_inv : mpn_lshift_safety_wit_45_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_46_nonalias_inv : mpn_lshift_safety_wit_46_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_47_inplace_inv : mpn_lshift_safety_wit_47_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_48_off_zero_inv : mpn_lshift_safety_wit_48_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_49_off_pos_inv : mpn_lshift_safety_wit_49_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_50_nonalias_inv : mpn_lshift_safety_wit_50_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_51_inplace_inv : mpn_lshift_safety_wit_51_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_52_off_zero_inv : mpn_lshift_safety_wit_52_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_53_off_pos_inv : mpn_lshift_safety_wit_53_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_1_nonalias : mpn_lshift_entail_wit_1_nonalias.
Axiom proof_of_mpn_lshift_entail_wit_2_inplace : mpn_lshift_entail_wit_2_inplace.
Axiom proof_of_mpn_lshift_entail_wit_3_nonalias : mpn_lshift_entail_wit_3_nonalias.
Axiom proof_of_mpn_lshift_entail_wit_4_inplace : mpn_lshift_entail_wit_4_inplace.
Axiom proof_of_mpn_lshift_entail_wit_5_off_zero : mpn_lshift_entail_wit_5_off_zero.
Axiom proof_of_mpn_lshift_entail_wit_6_off_pos : mpn_lshift_entail_wit_6_off_pos.
Axiom proof_of_mpn_lshift_entail_wit_7_nonalias_inv : mpn_lshift_entail_wit_7_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_8_inplace_inv : mpn_lshift_entail_wit_8_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_9_off_zero_inv : mpn_lshift_entail_wit_9_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_10_off_pos_inv : mpn_lshift_entail_wit_10_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_11_nonalias_inv : mpn_lshift_entail_wit_11_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_12_inplace_inv : mpn_lshift_entail_wit_12_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_13_off_zero_inv : mpn_lshift_entail_wit_13_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_14_off_pos_inv : mpn_lshift_entail_wit_14_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_15_nonalias_inv : mpn_lshift_entail_wit_15_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_16_inplace_inv : mpn_lshift_entail_wit_16_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_17_off_zero_inv : mpn_lshift_entail_wit_17_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_18_off_pos_inv : mpn_lshift_entail_wit_18_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_19_nonalias_inv : mpn_lshift_entail_wit_19_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_20_inplace_inv : mpn_lshift_entail_wit_20_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_21_off_zero_inv : mpn_lshift_entail_wit_21_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_22_off_pos_inv : mpn_lshift_entail_wit_22_off_pos_inv.
Axiom proof_of_mpn_lshift_return_wit_1_nonalias_inv : mpn_lshift_return_wit_1_nonalias_inv.
Axiom proof_of_mpn_lshift_return_wit_2_inplace_inv : mpn_lshift_return_wit_2_inplace_inv.
Axiom proof_of_mpn_lshift_return_wit_3_off_zero_inv : mpn_lshift_return_wit_3_off_zero_inv.
Axiom proof_of_mpn_lshift_return_wit_4_off_pos_inv : mpn_lshift_return_wit_4_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_1_shifted : mpn_lshift_partial_solve_wit_1_shifted.
Axiom proof_of_mpn_lshift_partial_solve_wit_2_nonalias : mpn_lshift_partial_solve_wit_2_nonalias.
Axiom proof_of_mpn_lshift_partial_solve_wit_3_inplace : mpn_lshift_partial_solve_wit_3_inplace.
Axiom proof_of_mpn_lshift_partial_solve_wit_4_off_zero : mpn_lshift_partial_solve_wit_4_off_zero.
Axiom proof_of_mpn_lshift_partial_solve_wit_5_off_pos : mpn_lshift_partial_solve_wit_5_off_pos.
Axiom proof_of_mpn_lshift_partial_solve_wit_6_nonalias_pure : mpn_lshift_partial_solve_wit_6_nonalias_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_6_nonalias : mpn_lshift_partial_solve_wit_6_nonalias.
Axiom proof_of_mpn_lshift_partial_solve_wit_7_inplace_pure : mpn_lshift_partial_solve_wit_7_inplace_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_7_inplace : mpn_lshift_partial_solve_wit_7_inplace.
Axiom proof_of_mpn_lshift_partial_solve_wit_8_nonalias_inv : mpn_lshift_partial_solve_wit_8_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_9_inplace_inv : mpn_lshift_partial_solve_wit_9_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_10_off_zero_inv : mpn_lshift_partial_solve_wit_10_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_11_off_pos_inv : mpn_lshift_partial_solve_wit_11_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_12_nonalias_inv_pure : mpn_lshift_partial_solve_wit_12_nonalias_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_12_nonalias_inv : mpn_lshift_partial_solve_wit_12_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_13_inplace_inv_pure : mpn_lshift_partial_solve_wit_13_inplace_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_13_inplace_inv : mpn_lshift_partial_solve_wit_13_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_14_off_zero_inv_pure : mpn_lshift_partial_solve_wit_14_off_zero_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_14_off_zero_inv : mpn_lshift_partial_solve_wit_14_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_15_off_pos_inv_pure : mpn_lshift_partial_solve_wit_15_off_pos_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_15_off_pos_inv : mpn_lshift_partial_solve_wit_15_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_16_nonalias_inv : mpn_lshift_partial_solve_wit_16_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_17_inplace_inv : mpn_lshift_partial_solve_wit_17_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_18_off_zero_inv : mpn_lshift_partial_solve_wit_18_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_19_off_pos_inv : mpn_lshift_partial_solve_wit_19_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_20_nonalias_inv_pure : mpn_lshift_partial_solve_wit_20_nonalias_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_20_nonalias_inv : mpn_lshift_partial_solve_wit_20_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_21_inplace_inv_pure : mpn_lshift_partial_solve_wit_21_inplace_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_21_inplace_inv : mpn_lshift_partial_solve_wit_21_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_22_off_zero_inv_pure : mpn_lshift_partial_solve_wit_22_off_zero_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_22_off_zero_inv : mpn_lshift_partial_solve_wit_22_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_23_off_pos_inv_pure : mpn_lshift_partial_solve_wit_23_off_pos_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_23_off_pos_inv : mpn_lshift_partial_solve_wit_23_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_24_nonalias_inv : mpn_lshift_partial_solve_wit_24_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_25_inplace_inv : mpn_lshift_partial_solve_wit_25_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_26_off_zero_inv : mpn_lshift_partial_solve_wit_26_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_27_off_pos_inv : mpn_lshift_partial_solve_wit_27_off_pos_inv.
Axiom proof_of_mpn_lshift_which_implies_wit_1 : mpn_lshift_which_implies_wit_1.
Axiom proof_of_mpn_lshift_which_implies_wit_2 : mpn_lshift_which_implies_wit_2.
Axiom proof_of_mpn_lshift_which_implies_wit_3 : mpn_lshift_which_implies_wit_3.
Axiom proof_of_mpn_lshift_which_implies_wit_4 : mpn_lshift_which_implies_wit_4.
Axiom proof_of_mpn_lshift_which_implies_wit_5 : mpn_lshift_which_implies_wit_5.
Axiom proof_of_mpn_lshift_which_implies_wit_6 : mpn_lshift_which_implies_wit_6.
Axiom proof_of_mpn_lshift_which_implies_wit_7 : mpn_lshift_which_implies_wit_7.
Axiom proof_of_mpn_lshift_which_implies_wit_8 : mpn_lshift_which_implies_wit_8.
Axiom proof_of_mpn_lshift_which_implies_wit_9 : mpn_lshift_which_implies_wit_9.
Axiom proof_of_mpn_lshift_which_implies_wit_10 : mpn_lshift_which_implies_wit_10.
Axiom proof_of_mpn_lshift_which_implies_wit_11 : mpn_lshift_which_implies_wit_11.

End VC_Correct.
