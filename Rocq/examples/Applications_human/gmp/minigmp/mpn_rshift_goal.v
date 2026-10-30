From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_rshift -----*)

Definition mpn_rshift_safety_wit_1 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )),
  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_rshift_safety_wit_2 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_3 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> (up_pre + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
|--
  “ ((32 - cnt_pre ) <= 31) ”
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_rshift_safety_wit_4 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> (up_pre + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_rshift_safety_wit_5 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> (up_pre + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre))
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_rshift_safety_wit_6 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i: Z) (rp: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = ((n_pre - i ) - 1 ))) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : ((Zlength (l_done)) = i)) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH18 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH19 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH20 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> up)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_7 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> up)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_8 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_9 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (tnc <= 31) ”
  &&  “ (0 <= tnc) ”
.

Definition mpn_rshift_safety_wit_10 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> (rp + (1 * sizeof(UINT))))
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (cnt_pre <= 31) ”
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_rshift_safety_wit_11 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> (rp + (1 * sizeof(UINT))))
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre))
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_rshift_safety_wit_12 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> up)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_entail_wit_1 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) (i: Z),
  “ ((up_pre + (1 * sizeof(UINT))) = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ ((n_pre - 1 ) = ((n_pre - i ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (i = 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (l_done = (@nil Z)) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + 0 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) ((@nil Z))) + ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + 0 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ ((Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) = (Znth ((off_shifted + 0 )) (l_up_shifted) (0))) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (UIntArray.seg rp_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_1_split_goal_1 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + 0 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) ((@nil Z))) + ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_2 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_3 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + 0 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_4 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) = (Znth ((off_shifted + 0 )) (l_up_shifted) (0))) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_5 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_6 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_spatial :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  (UIntArray.seg rp_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_entail_wit_2 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i_2: Z) (l_done_2: (@list Z)) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH2 : (n = ((n_pre - i_2 ) - 1 ))) (PreH3 : (off_shifted >= 0)) (PreH4 : (n_pre > 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (tnc = (32 - cnt_pre ))) (PreH9 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (i_2 = 0)) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : (l_done_2 = (@nil Z))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) (i: Z),
  “ (rp_pre = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i_2: Z) (l_done_2: (@list Z)) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH2 : (n = ((n_pre - i_2 ) - 1 ))) (PreH3 : (off_shifted >= 0)) (PreH4 : (n_pre > 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (tnc = (32 - cnt_pre ))) (PreH9 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (i_2 = 0)) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : (l_done_2 = (@nil Z))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)),
  “ (rp_pre = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= (Zlength (l_done))) ”
  &&  “ ((Zlength (l_done)) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp_pre (Zlength (l_done)) (n_pre + off_shifted ) (sublist ((Zlength (l_done))) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_3 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n <> 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) (i: Z),
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (n <> 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n <> 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)),
  “ (rp = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ”
  &&  “ (n <> 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (0 <= (Zlength (l_done))) ”
  &&  “ (((Zlength (l_done)) + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp 0 1 (sublist ((Zlength (l_done))) (((Zlength (l_done)) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((Zlength (l_done)) + 1 ) ((off_shifted + (Zlength (l_done)) ) + 1 ) (sublist (((Zlength (l_done)) + 1 )) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + (Zlength (l_done)) ) + 1 )) (((off_shifted + (Zlength (l_done)) ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + (Zlength (l_done)) ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + (Zlength (l_done)) ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_4 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) (i_2: Z),
  “ ((rp + (1 * sizeof(UINT))) = (rp_pre + (i_2 * sizeof(UINT)))) ”
  &&  “ ((up + (1 * sizeof(UINT))) = (up_pre + ((i_2 + 1 ) * sizeof(UINT)))) ”
  &&  “ ((n - 1 ) = ((n_pre - i_2 ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i_2) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0))) ”
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i_2 l_done )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)),
  “ ((rp + (1 * sizeof(UINT))) = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ”
  &&  “ ((up + (1 * sizeof(UINT))) = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ”
  &&  “ ((n - 1 ) = ((n_pre - (Zlength (l_done)) ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= (Zlength (l_done))) ”
  &&  “ ((Zlength (l_done)) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ ((Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ”
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp_pre (Zlength (l_done)) (n_pre + off_shifted ) (sublist ((Zlength (l_done))) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_5 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i_2: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH3 : (n = ((n_pre - i_2 ) - 1 ))) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : ((Zlength (l_done_2)) = i_2)) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH18 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH19 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH20 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) (i: Z),
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i_2: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH3 : (n = ((n_pre - i_2 ) - 1 ))) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : ((Zlength (l_done_2)) = i_2)) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH18 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH19 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH20 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)),
  “ (rp = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= (Zlength (l_done))) ”
  &&  “ ((Zlength (l_done)) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp_pre (Zlength (l_done)) (n_pre + off_shifted ) (sublist ((Zlength (l_done))) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_6 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n = 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) (i: Z),
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = 0) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n = 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)),
  “ (rp = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = 0) ”
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= (Zlength (l_done))) ”
  &&  “ ((Zlength (l_done)) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp 0 1 (sublist ((Zlength (l_done))) (((Zlength (l_done)) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((Zlength (l_done)) + 1 ) (n_pre + off_shifted ) (sublist (((Zlength (l_done)) + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_7 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.full rp 1 (replace_Znth (0) (low_limb) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_out: (@list Z)),
  “ (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + (n_pre * sizeof(UINT)))) ”
  &&  “ (n = 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.full rp 1 (replace_Znth (0) (low_limb) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_out: (@list Z)),
  “ (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + (n_pre * sizeof(UINT)))) ”
  &&  “ (n = 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_return_wit_1 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_out_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (retval: Z) (PreH1 : (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT))))) (PreH2 : (up = (up_pre + (n_pre * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH12 : ((Zlength (l_out_2)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_out_2 )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 n_pre l_out_2 )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_1_pure :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )),
  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
.

Definition mpn_rshift_partial_solve_wit_1_aux :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
.

Definition mpn_rshift_partial_solve_wit_1 := mpn_rshift_partial_solve_wit_1_pure -> mpn_rshift_partial_solve_wit_1_aux.

Definition mpn_rshift_partial_solve_wit_2 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )),
  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre 0 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_3 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (n <> 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (((up + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up 0 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_4 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (n <> 0) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (0 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (((rp + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp 0 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_5 :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))),
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ”
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ”
  &&  “ (n = 0) ”
  &&  “ (n = ((n_pre - i ) - 1 )) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (tnc = (32 - cnt_pre )) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ ((Zlength (l_done)) = i) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  “ (list_within_bound UINT_MOD l_done ) ”
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ”
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (((rp + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp 0 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_which_implies_wit_1 :=
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (off_shifted >= 0)) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))),
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (off_shifted >= 0)) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))),
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_which_implies_wit_1_split_goal_spatial :=
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (PreH1 : (off_shifted >= 0)) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))),
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

(* Shallow FunAssertion specs for mpn_rshift. *)
Definition mpn_rshift_sig : FuncSig := ([ * u32;  * u32; i32; u32], u32)%ctype.

Definition mpn_rshift_shifted : Spec mpn_rshift_sig :=
  fun F =>
ALL (l_up: (@list Z)),
ALL (off: Z),
HoareFun ([ * u32;  * u32; i32; u32], u32)%ctype
  (fun '(rp_pre, (up_pre, (n_pre, cnt_pre))) =>
  (“ (n_pre > 0) ”
  &&  “ ((n_pre + off ) <= INT_MAX) ”
  &&  “ (off >= 0) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (up_pre = (rp_pre + (off * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up)) = (n_pre + off )) ”
  &&  “ (list_within_bound UINT_MOD l_up ) ”
  &&  (UIntArray.full rp_pre (n_pre + off ) l_up )))
  (fun '(rp_pre, (up_pre, (n_pre, cnt_pre))) retval =>
  (EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off) (l_up) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off) ((off + n_pre )) (l_up)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off ) (sublist (n_pre) ((n_pre + off )) (l_up)) )))
  F.

Definition mpn_rshift_inplace : Spec mpn_rshift_sig :=
  fun F =>
ALL (l_up: (@list Z)),
HoareFun ([ * u32;  * u32; i32; u32], u32)%ctype
  (fun '(rp_pre, (up_pre, (n_pre, cnt_pre))) =>
  (“ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up ) ”
  &&  (UIntArray.full up_pre n_pre l_up )))
  (fun '(rp_pre, (up_pre, (n_pre, cnt_pre))) retval =>
  (EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_up)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )))
  F.

Definition mpn_rshift_shifted_entail_inplace :=
forall (rp_pre: Z) (up_pre: Z) (n_pre: Z) (cnt_pre: Z) (l_up_inplace: (@list Z)),
  (“ (rp_pre = up_pre) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (UIntArray.full up_pre n_pre l_up_inplace ))
|--
EX (l_up_shifted: (@list Z))(off_shifted: Z),
  (“ (n_pre > 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (off_shifted >= 0) ”
  &&  “ (1 <= cnt_pre) ”
  &&  “ (cnt_pre < 32) ”
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted ))
  **
  (ALL (retval: Z),
  (EX (l_out_2: (@list Z)),
  “ ((Zlength (l_out_2)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out_2 ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.seg rp_pre 0 n_pre l_out_2 )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) ))
  -*
  (EX (l_out: (@list Z)),
  “ ((Zlength (l_out)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l_up_inplace)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_rshift_safety_wit_1 : mpn_rshift_safety_wit_1.
Axiom proof_of_mpn_rshift_safety_wit_2 : mpn_rshift_safety_wit_2.
Axiom proof_of_mpn_rshift_safety_wit_3 : mpn_rshift_safety_wit_3.
Axiom proof_of_mpn_rshift_safety_wit_4 : mpn_rshift_safety_wit_4.
Axiom proof_of_mpn_rshift_safety_wit_5 : mpn_rshift_safety_wit_5.
Axiom proof_of_mpn_rshift_safety_wit_6 : mpn_rshift_safety_wit_6.
Axiom proof_of_mpn_rshift_safety_wit_7 : mpn_rshift_safety_wit_7.
Axiom proof_of_mpn_rshift_safety_wit_8 : mpn_rshift_safety_wit_8.
Axiom proof_of_mpn_rshift_safety_wit_9 : mpn_rshift_safety_wit_9.
Axiom proof_of_mpn_rshift_safety_wit_10 : mpn_rshift_safety_wit_10.
Axiom proof_of_mpn_rshift_safety_wit_11 : mpn_rshift_safety_wit_11.
Axiom proof_of_mpn_rshift_safety_wit_12 : mpn_rshift_safety_wit_12.
Axiom proof_of_mpn_rshift_entail_wit_1 : mpn_rshift_entail_wit_1.
Axiom proof_of_mpn_rshift_entail_wit_2 : mpn_rshift_entail_wit_2.
Axiom proof_of_mpn_rshift_entail_wit_3 : mpn_rshift_entail_wit_3.
Axiom proof_of_mpn_rshift_entail_wit_4 : mpn_rshift_entail_wit_4.
Axiom proof_of_mpn_rshift_entail_wit_5 : mpn_rshift_entail_wit_5.
Axiom proof_of_mpn_rshift_entail_wit_6 : mpn_rshift_entail_wit_6.
Axiom proof_of_mpn_rshift_entail_wit_7 : mpn_rshift_entail_wit_7.
Axiom proof_of_mpn_rshift_return_wit_1 : mpn_rshift_return_wit_1.
Axiom proof_of_mpn_rshift_partial_solve_wit_1_pure : mpn_rshift_partial_solve_wit_1_pure.
Axiom proof_of_mpn_rshift_partial_solve_wit_1 : mpn_rshift_partial_solve_wit_1.
Axiom proof_of_mpn_rshift_partial_solve_wit_2 : mpn_rshift_partial_solve_wit_2.
Axiom proof_of_mpn_rshift_partial_solve_wit_3 : mpn_rshift_partial_solve_wit_3.
Axiom proof_of_mpn_rshift_partial_solve_wit_4 : mpn_rshift_partial_solve_wit_4.
Axiom proof_of_mpn_rshift_partial_solve_wit_5 : mpn_rshift_partial_solve_wit_5.
Axiom proof_of_mpn_rshift_which_implies_wit_1 : mpn_rshift_which_implies_wit_1.
Axiom proof_of_mpn_rshift_shifted_entail_inplace : mpn_rshift_shifted_entail_inplace.

End VC_Correct.
