Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_div_qr_preinv -----*)

Definition mpn_div_qr_preinv_safety_wit_1 := 
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (qp0 = qp_pre)) (PreH2 : (np0 = np_pre)) (PreH3 : (dp0 = dp_pre)) (PreH4 : (inv0 = inv_pre)) (PreH5 : (nn0 = nn_pre)) (PreH6 : (dn0 = dn_pre)) (PreH7 : (dn_pre > 0)) (PreH8 : (dn_pre <= nn_pre)) (PreH9 : (nn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_np)) = nn_pre)) (PreH11 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_preinv_safety_wit_2 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn0 = 1)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_preinv_safety_wit_3 := 
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre <> 1)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (inv0 = inv_pre)) (PreH6 : (nn0 = nn_pre)) (PreH7 : (dn0 = dn_pre)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= nn_pre)) (PreH10 : (nn_pre <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn_pre)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_preinv_safety_wit_4 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (dn0 > 2)) (PreH2 : (dn0 <= nn0)) (PreH3 : (nn0 <= INT_MAX)) (PreH4 : (0 < d_orig)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : ((Zlength (l_np)) = nn0)) (PreH8 : ((Zlength (l_dp)) = dn0)) (PreH9 : (list_within_bound UINT_MOD l_np )) (PreH10 : (list_within_bound UINT_MOD l_dp )) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH12 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH13 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH14 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH15 : (d1_orig <= UINT_MAX)) (PreH16 : (0 <= d0_orig)) (PreH17 : (d0_orig <= UINT_MAX)) (PreH18 : (0 <= di_orig)) (PreH19 : (di_orig <= UINT_MAX)) (PreH20 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH21 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |->_)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_preinv_safety_wit_5 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : (0 < d_orig)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH13 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH14 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH15 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH16 : (d1_orig <= UINT_MAX)) (PreH17 : (0 <= d0_orig)) (PreH18 : (d0_orig <= UINT_MAX)) (PreH19 : (0 <= di_orig)) (PreH20 : (di_orig <= UINT_MAX)) (PreH21 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH22 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |->_)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_preinv_safety_wit_6 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (rv: Z) (qv: Z) (l_tail: (@list Z)) (l_rem: (@list Z)) (l_q: (@list Z)) (PreH1 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH2 : ((Zlength (l_rem)) = dn0)) (PreH3 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH4 : (list_within_bound UINT_MOD l_q )) (PreH5 : (list_within_bound UINT_MOD l_rem )) (PreH6 : (list_within_bound UINT_MOD l_tail )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH9 : (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH10 : (0 <= rv)) (PreH11 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) (PreH12 : ((Zlength (l_out)) = nn0)) (PreH13 : (list_within_bound UINT_MOD l_out )) (PreH14 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH15 : (shift_orig > 0)) (PreH16 : (dn0 > 2)) (PreH17 : (dn0 <= nn0)) (PreH18 : (nn0 <= INT_MAX)) (PreH19 : (0 < d_orig)) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : ((Zlength (l_np)) = nn0)) (PreH23 : ((Zlength (l_dp)) = dn0)) (PreH24 : (list_within_bound UINT_MOD l_np )) (PreH25 : (list_within_bound UINT_MOD l_dp )) (PreH26 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH27 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH28 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH29 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH30 : (d1_orig <= UINT_MAX)) (PreH31 : (0 <= d0_orig)) (PreH32 : (d0_orig <= UINT_MAX)) (PreH33 : (0 <= di_orig)) (PreH34 : (di_orig <= UINT_MAX)) (PreH35 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH36 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_preinv_safety_wit_7 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (rv: Z) (qv: Z) (l_tail: (@list Z)) (l_rem: (@list Z)) (l_q: (@list Z)) (PreH1 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH2 : ((Zlength (l_rem)) = dn0)) (PreH3 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH4 : (list_within_bound UINT_MOD l_q )) (PreH5 : (list_within_bound UINT_MOD l_rem )) (PreH6 : (list_within_bound UINT_MOD l_tail )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH9 : (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH10 : (0 <= rv)) (PreH11 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) (PreH12 : (shift_orig <= 0)) (PreH13 : (dn0 > 2)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : (0 < d_orig)) (PreH17 : (0 <= shift_orig)) (PreH18 : (shift_orig < 32)) (PreH19 : ((Zlength (l_np)) = nn0)) (PreH20 : ((Zlength (l_dp)) = dn0)) (PreH21 : (list_within_bound UINT_MOD l_np )) (PreH22 : (list_within_bound UINT_MOD l_dp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH24 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH25 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH26 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH27 : (d1_orig <= UINT_MAX)) (PreH28 : (0 <= d0_orig)) (PreH29 : (d0_orig <= UINT_MAX)) (PreH30 : (0 <= di_orig)) (PreH31 : (di_orig <= UINT_MAX)) (PreH32 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH33 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_preinv_safety_wit_8 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (rv: Z) (qv: Z) (l_tail: (@list Z)) (l_rem: (@list Z)) (l_q: (@list Z)) (PreH1 : (shift_orig <= 0)) (PreH2 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem)) = dn0)) (PreH4 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q )) (PreH6 : (list_within_bound UINT_MOD l_rem )) (PreH7 : (list_within_bound UINT_MOD l_tail )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH10 : (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH11 : (0 <= rv)) (PreH12 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) (PreH13 : ((Zlength (l_out)) = nn0)) (PreH14 : (list_within_bound UINT_MOD l_out )) (PreH15 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH16 : (shift_orig > 0)) (PreH17 : (dn0 > 2)) (PreH18 : (dn0 <= nn0)) (PreH19 : (nn0 <= INT_MAX)) (PreH20 : (0 < d_orig)) (PreH21 : (0 <= shift_orig)) (PreH22 : (shift_orig < 32)) (PreH23 : ((Zlength (l_np)) = nn0)) (PreH24 : ((Zlength (l_dp)) = dn0)) (PreH25 : (list_within_bound UINT_MOD l_np )) (PreH26 : (list_within_bound UINT_MOD l_dp )) (PreH27 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH28 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH29 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH30 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH31 : (d1_orig <= UINT_MAX)) (PreH32 : (0 <= d0_orig)) (PreH33 : (d0_orig <= UINT_MAX)) (PreH34 : (0 <= di_orig)) (PreH35 : (di_orig <= UINT_MAX)) (PreH36 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH37 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition mpn_div_qr_preinv_safety_wit_9 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (rv: Z) (qv: Z) (l_tail: (@list Z)) (l_rem: (@list Z)) (l_q: (@list Z)) (PreH1 : (shift_orig > 0)) (PreH2 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem)) = dn0)) (PreH4 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q )) (PreH6 : (list_within_bound UINT_MOD l_rem )) (PreH7 : (list_within_bound UINT_MOD l_tail )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH10 : (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH11 : (0 <= rv)) (PreH12 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) (PreH13 : (shift_orig <= 0)) (PreH14 : (dn0 > 2)) (PreH15 : (dn0 <= nn0)) (PreH16 : (nn0 <= INT_MAX)) (PreH17 : (0 < d_orig)) (PreH18 : (0 <= shift_orig)) (PreH19 : (shift_orig < 32)) (PreH20 : ((Zlength (l_np)) = nn0)) (PreH21 : ((Zlength (l_dp)) = dn0)) (PreH22 : (list_within_bound UINT_MOD l_np )) (PreH23 : (list_within_bound UINT_MOD l_dp )) (PreH24 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH25 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH26 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH27 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH28 : (d1_orig <= UINT_MAX)) (PreH29 : (0 <= d0_orig)) (PreH30 : (d0_orig <= UINT_MAX)) (PreH31 : (0 <= di_orig)) (PreH32 : (di_orig <= UINT_MAX)) (PreH33 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH34 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition mpn_div_qr_preinv_entail_wit_1 := 
(
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 1)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (inv0 = inv_pre)) (PreH6 : (nn0 = nn_pre)) (PreH7 : (dn0 = dn_pre)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= nn_pre)) (PreH10 : (nn_pre <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn_pre)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ (dn0 = 1) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
) \/
(
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 1)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (inv0 = inv_pre)) (PreH6 : (nn0 = nn_pre)) (PreH7 : (dn0 = dn_pre)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= nn_pre)) (PreH10 : (nn_pre <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn_pre)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ ((Zlength (l_np)) = nn0) ”
  &&  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
).

Definition mpn_div_qr_preinv_entail_wit_1_split_goal_1 := 
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 1)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (inv0 = inv_pre)) (PreH6 : (nn0 = nn_pre)) (PreH7 : (dn0 = dn_pre)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= nn_pre)) (PreH10 : (nn_pre <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn_pre)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ ((Zlength (l_np)) = nn0) ”
.

Definition mpn_div_qr_preinv_entail_wit_1_split_goal_spatial := 
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 1)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (inv0 = inv_pre)) (PreH6 : (nn0 = nn_pre)) (PreH7 : (dn0 = dn_pre)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= nn_pre)) (PreH10 : (nn_pre <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn_pre)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
.

Definition mpn_div_qr_preinv_entail_wit_2 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (qv_2: Z) (l_q_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_q_2)) = nn0)) (PreH2 : (list_within_bound UINT_MOD l_q_2 )) (PreH3 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH4 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + retval ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < d_orig)) (PreH7 : (dn0 = 1)) (PreH8 : (dn0 > 0)) (PreH9 : (dn0 <= nn0)) (PreH10 : (nn0 <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  (UIntArray.full np0 nn0 (replace_Znth (0) (retval) (l_np)) )
  **  (optional_q_full qp0 nn0 l_q_2 )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dn0 = 1) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (qv_2: Z) (l_q_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_q_2)) = nn0)) (PreH2 : (list_within_bound UINT_MOD l_q_2 )) (PreH3 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH4 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + retval ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < d_orig)) (PreH7 : (dn0 = 1)) (PreH8 : (dn0 > 0)) (PreH9 : (dn0 <= nn0)) (PreH10 : (nn0 <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  (UIntArray.full np0 nn0 (replace_Znth (0) (retval) (l_np)) )
  **  (optional_q_full qp0 nn0 l_q_2 )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
|--
  EX (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dn0 = 1) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
).

Definition mpn_div_qr_preinv_entail_wit_3 := 
(
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (qp0 = qp_pre)) (PreH4 : (np0 = np_pre)) (PreH5 : (dp0 = dp_pre)) (PreH6 : (inv0 = inv_pre)) (PreH7 : (nn0 = nn_pre)) (PreH8 : (dn0 = dn_pre)) (PreH9 : (dn_pre > 0)) (PreH10 : (dn_pre <= nn_pre)) (PreH11 : (nn_pre <= INT_MAX)) (PreH12 : ((Zlength (l_np)) = nn_pre)) (PreH13 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ (dn0 = 2) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 (nn0 - 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
) \/
(
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (qp0 = qp_pre)) (PreH4 : (np0 = np_pre)) (PreH5 : (dp0 = dp_pre)) (PreH6 : (inv0 = inv_pre)) (PreH7 : (nn0 = nn_pre)) (PreH8 : (dn0 = dn_pre)) (PreH9 : (dn_pre > 0)) (PreH10 : (dn_pre <= nn_pre)) (PreH11 : (nn_pre <= INT_MAX)) (PreH12 : ((Zlength (l_np)) = nn_pre)) (PreH13 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ ((Zlength (l_np)) = nn0) ”
  &&  (optional_q_undef qp0 (nn0 - 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
).

Definition mpn_div_qr_preinv_entail_wit_3_split_goal_1 := 
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (qp0 = qp_pre)) (PreH4 : (np0 = np_pre)) (PreH5 : (dp0 = dp_pre)) (PreH6 : (inv0 = inv_pre)) (PreH7 : (nn0 = nn_pre)) (PreH8 : (dn0 = dn_pre)) (PreH9 : (dn_pre > 0)) (PreH10 : (dn_pre <= nn_pre)) (PreH11 : (nn_pre <= INT_MAX)) (PreH12 : ((Zlength (l_np)) = nn_pre)) (PreH13 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  “ ((Zlength (l_np)) = nn0) ”
.

Definition mpn_div_qr_preinv_entail_wit_3_split_goal_spatial := 
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (qp0 = qp_pre)) (PreH4 : (np0 = np_pre)) (PreH5 : (dp0 = dp_pre)) (PreH6 : (inv0 = inv_pre)) (PreH7 : (nn0 = nn_pre)) (PreH8 : (dn0 = dn_pre)) (PreH9 : (dn_pre > 0)) (PreH10 : (dn_pre <= nn_pre)) (PreH11 : (nn_pre <= INT_MAX)) (PreH12 : ((Zlength (l_np)) = nn_pre)) (PreH13 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  (optional_q_undef qp0 (nn0 - 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
.

Definition mpn_div_qr_preinv_entail_wit_4 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : ((Zlength (l_q_2)) = (nn0 - 1 ))) (PreH2 : ((Zlength (l_rem_2)) = 2)) (PreH3 : ((Zlength (l_tail_2)) = (nn0 - 2 ))) (PreH4 : (list_within_bound UINT_MOD l_q_2 )) (PreH5 : (list_within_bound UINT_MOD l_rem_2 )) (PreH6 : (list_within_bound UINT_MOD l_tail_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH10 : (0 <= rv_2)) (PreH11 : (rv_2 < d_orig)) (PreH12 : (dn0 = 2)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_full qp0 (nn0 - 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 2 l_rem_2 )
  **  (UIntArray.seg np0 2 nn0 l_tail_2 )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dn0 = 2) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : ((Zlength (l_q_2)) = (nn0 - 1 ))) (PreH2 : ((Zlength (l_rem_2)) = 2)) (PreH3 : ((Zlength (l_tail_2)) = (nn0 - 2 ))) (PreH4 : (list_within_bound UINT_MOD l_q_2 )) (PreH5 : (list_within_bound UINT_MOD l_rem_2 )) (PreH6 : (list_within_bound UINT_MOD l_tail_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH10 : (0 <= rv_2)) (PreH11 : (rv_2 < d_orig)) (PreH12 : (dn0 = 2)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_full qp0 (nn0 - 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 2 l_rem_2 )
  **  (UIntArray.seg np0 2 nn0 l_tail_2 )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
|--
  EX (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dn0 = 2) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
).

Definition mpn_div_qr_preinv_entail_wit_5 := 
(
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (qp0 = qp_pre)) (PreH4 : (np0 = np_pre)) (PreH5 : (dp0 = dp_pre)) (PreH6 : (inv0 = inv_pre)) (PreH7 : (nn0 = nn_pre)) (PreH8 : (dn0 = dn_pre)) (PreH9 : (dn_pre > 0)) (PreH10 : (dn_pre <= nn_pre)) (PreH11 : (nn_pre <= INT_MAX)) (PreH12 : ((Zlength (l_np)) = nn_pre)) (PreH13 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (l_dp: (@list Z))  (shift_orig: Z) ,
  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ”
  &&  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (inv_pre: Z) (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (qp0 = qp_pre)) (PreH4 : (np0 = np_pre)) (PreH5 : (dp0 = dp_pre)) (PreH6 : (inv0 = inv_pre)) (PreH7 : (nn0 = nn_pre)) (PreH8 : (dn0 = dn_pre)) (PreH9 : (dn_pre > 0)) (PreH10 : (dn_pre <= nn_pre)) (PreH11 : (nn_pre <= INT_MAX)) (PreH12 : ((Zlength (l_np)) = nn_pre)) (PreH13 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (store_preinv_divisor dp_pre inv_pre dn_pre d_orig )
|--
  EX (di_orig: Z)  (l_dp: (@list Z))  (shift_orig: Z) ,
  “ (inv_pre = inv0) ” 
  &&  “ (dn_pre = dn0) ” 
  &&  “ (dp_pre = dp0) ” 
  &&  “ (nn_pre = nn0) ” 
  &&  “ (np_pre = np0) ” 
  &&  “ (qp_pre = qp0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth ((dn0 - 1 )) (l_dp) (0)))
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth ((dn0 - 2 )) (l_dp) (0)))
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
).

Definition mpn_div_qr_preinv_entail_wit_6 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp_2: (@list Z)) (shift_orig: Z) (d1_orig_2: Z) (d0_orig_2: Z) (di_orig_2: Z) (l_out: (@list Z)) (retval: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : (shift_orig > 0)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) = ((qv_2 * (list_to_Z (UINT_MOD) (l_dp_2)) ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < (list_to_Z (UINT_MOD) (l_dp_2)))) (PreH13 : ((Zlength (l_out)) = nn0)) (PreH14 : (list_within_bound UINT_MOD l_out )) (PreH15 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH16 : (shift_orig > 0)) (PreH17 : (dn0 > 2)) (PreH18 : (dn0 <= nn0)) (PreH19 : (nn0 <= INT_MAX)) (PreH20 : (0 < d_orig)) (PreH21 : (0 <= shift_orig)) (PreH22 : (shift_orig < 32)) (PreH23 : ((Zlength (l_np)) = nn0)) (PreH24 : ((Zlength (l_dp_2)) = dn0)) (PreH25 : (list_within_bound UINT_MOD l_np )) (PreH26 : (list_within_bound UINT_MOD l_dp_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_dp_2)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH28 : (d1_orig_2 = (Znth ((dn0 - 1 )) (l_dp_2) (0)))) (PreH29 : (d0_orig_2 = (Znth ((dn0 - 2 )) (l_dp_2) (0)))) (PreH30 : ((UINT_MOD ÷ 2 ) <= d1_orig_2)) (PreH31 : (d1_orig_2 <= UINT_MAX)) (PreH32 : (0 <= d0_orig_2)) (PreH33 : (d0_orig_2 <= UINT_MAX)) (PreH34 : (0 <= di_orig_2)) (PreH35 : (di_orig_2 <= UINT_MAX)) (PreH36 : (((di_orig_2 + UINT_MOD ) * ((UINT_MOD * d1_orig_2 ) + d0_orig_2 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH37 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig_2 ) + d0_orig_2 ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (UIntArray.full dp0 dn0 l_dp_2 )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig_2)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig_2)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig_2)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z))  (l_norm: (@list Z))  (di_orig: Z)  (d0_orig: Z)  (l_dp: (@list Z))  (d1_orig: Z) ,
  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_norm)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_norm ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_norm)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < (list_to_Z (UINT_MOD) (l_dp))) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.full np0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (np0: Z) (qp0: Z) (l_dp_2: (@list Z)) (shift_orig: Z) (d1_orig_2: Z) (d0_orig_2: Z) (di_orig_2: Z) (l_out: (@list Z)) (retval: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : (shift_orig > 0)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) = ((qv_2 * (list_to_Z (UINT_MOD) (l_dp_2)) ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < (list_to_Z (UINT_MOD) (l_dp_2)))) (PreH13 : ((Zlength (l_out)) = nn0)) (PreH14 : (list_within_bound UINT_MOD l_out )) (PreH15 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH16 : (shift_orig > 0)) (PreH17 : (dn0 > 2)) (PreH18 : (dn0 <= nn0)) (PreH19 : (nn0 <= INT_MAX)) (PreH20 : (0 < d_orig)) (PreH21 : (0 <= shift_orig)) (PreH22 : (shift_orig < 32)) (PreH23 : ((Zlength (l_np)) = nn0)) (PreH24 : ((Zlength (l_dp_2)) = dn0)) (PreH25 : (list_within_bound UINT_MOD l_np )) (PreH26 : (list_within_bound UINT_MOD l_dp_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_dp_2)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH28 : (d1_orig_2 = (Znth ((dn0 - 1 )) (l_dp_2) (0)))) (PreH29 : (d0_orig_2 = (Znth ((dn0 - 2 )) (l_dp_2) (0)))) (PreH30 : ((UINT_MOD ÷ 2 ) <= d1_orig_2)) (PreH31 : (d1_orig_2 <= UINT_MAX)) (PreH32 : (0 <= d0_orig_2)) (PreH33 : (d0_orig_2 <= UINT_MAX)) (PreH34 : (0 <= di_orig_2)) (PreH35 : (di_orig_2 <= UINT_MAX)) (PreH36 : (((di_orig_2 + UINT_MOD ) * ((UINT_MOD * d1_orig_2 ) + d0_orig_2 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH37 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig_2 ) + d0_orig_2 ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
|--
  EX (l_rem: (@list Z))  (l_q: (@list Z))  (l_norm: (@list Z)) ,
  “ (d0_orig_2 = (Znth ((dn0 - 2 )) (l_dp_2) (0))) ” 
  &&  “ (d1_orig_2 = (Znth ((dn0 - 1 )) (l_dp_2) (0))) ” 
  &&  “ (d0_orig_2 = (Znth ((dn0 - 2 )) (l_dp_2) (0))) ” 
  &&  “ (d1_orig_2 = (Znth ((dn0 - 1 )) (l_dp_2) (0))) ” 
  &&  “ (d0_orig_2 = (Znth ((dn0 - 2 )) (l_dp_2) (0))) ” 
  &&  “ (d1_orig_2 = (Znth ((dn0 - 1 )) (l_dp_2) (0))) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth ((dn0 - 1 )) (l_dp_2) (0))) ” 
  &&  “ ((Znth ((dn0 - 1 )) (l_dp_2) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((dn0 - 2 )) (l_dp_2) (0))) ” 
  &&  “ ((Znth ((dn0 - 2 )) (l_dp_2) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= di_orig_2) ” 
  &&  “ (di_orig_2 <= UINT_MAX) ” 
  &&  “ (((di_orig_2 + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp_2) (0)) ) + (Znth ((dn0 - 2 )) (l_dp_2) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp_2) (0)) ) + (Znth ((dn0 - 2 )) (l_dp_2) (0)) ) )) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_norm)) = nn0) ” 
  &&  “ ((Zlength (l_dp_2)) = dn0) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_norm ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp_2)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_norm)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = (((list_to_Z (UINT_MOD) (l_q)) * (list_to_Z (UINT_MOD) (l_dp_2)) ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < (list_to_Z (UINT_MOD) (l_dp_2))) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.full np0 dn0 l_rem )
).

Definition mpn_div_qr_preinv_entail_wit_7 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = dn0)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (0) (l_rem) (0)) * (Z.pow (2) ((32 - shift ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) (l_rem)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (shift)) ) + (retval ÷ (Z.pow (2) ((32 - shift ))) ) ))) (PreH5 : (dn0 > 2)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : (0 < d_orig)) (PreH9 : (1 <= shift)) (PreH10 : (shift < 32)) (PreH11 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH12 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_norm)) = nn0)) (PreH23 : ((Zlength (l_dp)) = dn0)) (PreH24 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH25 : ((Zlength (l_rem)) = dn0)) (PreH26 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH27 : (list_within_bound UINT_MOD l_np )) (PreH28 : (list_within_bound UINT_MOD l_norm )) (PreH29 : (list_within_bound UINT_MOD l_dp )) (PreH30 : (list_within_bound UINT_MOD l_q )) (PreH31 : (list_within_bound UINT_MOD l_rem )) (PreH32 : (list_within_bound UINT_MOD l_tail )) (PreH33 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH34 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH35 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH36 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH37 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH38 : (0 <= rv)) (PreH39 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) ,
  (UIntArray.full np0 dn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
|--
  “ (0 = 0) ” 
  &&  “ (nh_orig <= UINT_MAX) ” 
  &&  “ (shift <= UINT_MAX) ” 
  &&  “ (di_orig >= 0) ” 
  &&  “ (d0_orig >= 0) ” 
  &&  “ (d1_orig >= 0) ” 
  &&  “ (nh_orig >= 0) ” 
  &&  “ (shift >= 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (dn0 >= INT_MIN) ” 
  &&  “ (nn0 >= INT_MIN) ” 
  &&  “ ((Zlength (l_out)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_rem) (0)) * (Z.pow (2) ((32 - shift ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (shift)) ) + (retval ÷ (Z.pow (2) ((32 - shift ))) ) )) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_norm)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_norm ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) )) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < (list_to_Z (UINT_MOD) (l_dp))) ”
  &&  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full np0 dn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (nh_orig <= UINT_MAX)) (PreH3 : (shift <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d0_orig >= 0)) (PreH7 : (d1_orig >= 0)) (PreH8 : (nh_orig >= 0)) (PreH9 : (shift >= 0)) (PreH10 : (dn0 <= INT_MAX)) (PreH11 : (dn0 >= INT_MIN)) (PreH12 : (nn0 >= INT_MIN)) (PreH13 : ((Zlength (l_out)) = dn0)) (PreH14 : (list_within_bound UINT_MOD l_out )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (0) (l_rem) (0)) * (Z.pow (2) ((32 - shift ))) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) (l_rem)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (shift)) ) + (retval ÷ (Z.pow (2) ((32 - shift ))) ) ))) (PreH17 : (dn0 > 2)) (PreH18 : (dn0 <= nn0)) (PreH19 : (nn0 <= INT_MAX)) (PreH20 : (0 < d_orig)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH33 : ((Zlength (l_np)) = nn0)) (PreH34 : ((Zlength (l_norm)) = nn0)) (PreH35 : ((Zlength (l_dp)) = dn0)) (PreH36 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH37 : ((Zlength (l_rem)) = dn0)) (PreH38 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH39 : (list_within_bound UINT_MOD l_np )) (PreH40 : (list_within_bound UINT_MOD l_norm )) (PreH41 : (list_within_bound UINT_MOD l_dp )) (PreH42 : (list_within_bound UINT_MOD l_q )) (PreH43 : (list_within_bound UINT_MOD l_rem )) (PreH44 : (list_within_bound UINT_MOD l_tail )) (PreH45 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH46 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH47 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH48 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH49 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH50 : (0 <= rv)) (PreH51 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) ,
  (UIntArray.full np0 dn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
|--
  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full np0 dn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
).

Definition mpn_div_qr_preinv_entail_wit_7_split_goal_spatial := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (nh_orig <= UINT_MAX)) (PreH3 : (shift <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d0_orig >= 0)) (PreH7 : (d1_orig >= 0)) (PreH8 : (nh_orig >= 0)) (PreH9 : (shift >= 0)) (PreH10 : (dn0 <= INT_MAX)) (PreH11 : (dn0 >= INT_MIN)) (PreH12 : (nn0 >= INT_MIN)) (PreH13 : ((Zlength (l_out)) = dn0)) (PreH14 : (list_within_bound UINT_MOD l_out )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (0) (l_rem) (0)) * (Z.pow (2) ((32 - shift ))) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) (l_rem)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (shift)) ) + (retval ÷ (Z.pow (2) ((32 - shift ))) ) ))) (PreH17 : (dn0 > 2)) (PreH18 : (dn0 <= nn0)) (PreH19 : (nn0 <= INT_MAX)) (PreH20 : (0 < d_orig)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH33 : ((Zlength (l_np)) = nn0)) (PreH34 : ((Zlength (l_norm)) = nn0)) (PreH35 : ((Zlength (l_dp)) = dn0)) (PreH36 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH37 : ((Zlength (l_rem)) = dn0)) (PreH38 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH39 : (list_within_bound UINT_MOD l_np )) (PreH40 : (list_within_bound UINT_MOD l_norm )) (PreH41 : (list_within_bound UINT_MOD l_dp )) (PreH42 : (list_within_bound UINT_MOD l_q )) (PreH43 : (list_within_bound UINT_MOD l_rem )) (PreH44 : (list_within_bound UINT_MOD l_tail )) (PreH45 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH46 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH47 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH48 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH49 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH50 : (0 <= rv)) (PreH51 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) ,
  (UIntArray.full np0 dn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
|--
  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full np0 dn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_preinv_return_wit_1 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (PreH1 : (dn0 = 1)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (PreH1 : (dn0 = 1)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
|--
  EX (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
).

Definition mpn_div_qr_preinv_return_wit_2 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (PreH1 : (dn0 = 2)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (PreH1 : (dn0 = 2)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
|--
  EX (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
).

Definition mpn_div_qr_preinv_return_wit_3 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem_2: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (0 = 0)) (PreH2 : (nh_orig <= UINT_MAX)) (PreH3 : (shift <= UINT_MAX)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (nh_orig >= 0)) (PreH8 : (shift >= 0)) (PreH9 : (dn0 <= INT_MAX)) (PreH10 : (dn0 >= INT_MIN)) (PreH11 : (nn0 >= INT_MIN)) (PreH12 : ((Zlength (l_out)) = dn0)) (PreH13 : (list_within_bound UINT_MOD l_out )) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_rem_2) (0)) * (Z.pow (2) ((32 - shift ))) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) (l_rem_2)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (shift)) ) + (retval ÷ (Z.pow (2) ((32 - shift ))) ) ))) (PreH16 : (dn0 > 2)) (PreH17 : (dn0 <= nn0)) (PreH18 : (nn0 <= INT_MAX)) (PreH19 : (0 < d_orig)) (PreH20 : (1 <= shift)) (PreH21 : (shift < 32)) (PreH22 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH23 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH24 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH25 : (d1_orig <= UINT_MAX)) (PreH26 : (0 <= d0_orig)) (PreH27 : (d0_orig <= UINT_MAX)) (PreH28 : (0 <= di_orig)) (PreH29 : (di_orig <= UINT_MAX)) (PreH30 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH31 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH32 : ((Zlength (l_np)) = nn0)) (PreH33 : ((Zlength (l_norm)) = nn0)) (PreH34 : ((Zlength (l_dp)) = dn0)) (PreH35 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH36 : ((Zlength (l_rem_2)) = dn0)) (PreH37 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH38 : (list_within_bound UINT_MOD l_np )) (PreH39 : (list_within_bound UINT_MOD l_norm )) (PreH40 : (list_within_bound UINT_MOD l_dp )) (PreH41 : (list_within_bound UINT_MOD l_q_2 )) (PreH42 : (list_within_bound UINT_MOD l_rem_2 )) (PreH43 : (list_within_bound UINT_MOD l_tail_2 )) (PreH44 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH45 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH46 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH47 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH48 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv_2 * (list_to_Z (UINT_MOD) (l_dp)) ) + rv_2 ))) (PreH49 : (0 <= rv_2)) (PreH50 : (rv_2 < (list_to_Z (UINT_MOD) (l_dp)))) ,
  (UIntArray.full np0 dn0 l_out )
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem_2: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (nh_orig <= UINT_MAX)) (PreH2 : (shift <= UINT_MAX)) (PreH3 : (di_orig >= 0)) (PreH4 : (d0_orig >= 0)) (PreH5 : (d1_orig >= 0)) (PreH6 : (nh_orig >= 0)) (PreH7 : (shift >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = dn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_rem_2) (0)) * (Z.pow (2) ((32 - shift ))) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) (l_rem_2)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (shift)) ) + (retval ÷ (Z.pow (2) ((32 - shift ))) ) ))) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (1 <= shift)) (PreH20 : (shift < 32)) (PreH21 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH22 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH23 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH24 : (d1_orig <= UINT_MAX)) (PreH25 : (0 <= d0_orig)) (PreH26 : (d0_orig <= UINT_MAX)) (PreH27 : (0 <= di_orig)) (PreH28 : (di_orig <= UINT_MAX)) (PreH29 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH30 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH31 : ((Zlength (l_np)) = nn0)) (PreH32 : ((Zlength (l_norm)) = nn0)) (PreH33 : ((Zlength (l_dp)) = dn0)) (PreH34 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH35 : ((Zlength (l_rem_2)) = dn0)) (PreH36 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH37 : (list_within_bound UINT_MOD l_np )) (PreH38 : (list_within_bound UINT_MOD l_norm )) (PreH39 : (list_within_bound UINT_MOD l_dp )) (PreH40 : (list_within_bound UINT_MOD l_q_2 )) (PreH41 : (list_within_bound UINT_MOD l_rem_2 )) (PreH42 : (list_within_bound UINT_MOD l_tail_2 )) (PreH43 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH44 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH45 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH46 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH47 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv_2 * (list_to_Z (UINT_MOD) (l_dp)) ) + rv_2 ))) (PreH48 : (0 <= rv_2)) (PreH49 : (rv_2 < (list_to_Z (UINT_MOD) (l_dp)))) ,
  (UIntArray.full np0 dn0 l_out )
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
).

Definition mpn_div_qr_preinv_return_wit_4 := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : (shift_orig <= 0)) (PreH2 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH3 : ((Zlength (l_rem_2)) = dn0)) (PreH4 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH5 : (list_within_bound UINT_MOD l_q_2 )) (PreH6 : (list_within_bound UINT_MOD l_rem_2 )) (PreH7 : (list_within_bound UINT_MOD l_tail_2 )) (PreH8 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH10 : (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) = ((qv_2 * (list_to_Z (UINT_MOD) (l_dp)) ) + rv_2 ))) (PreH11 : (0 <= rv_2)) (PreH12 : (rv_2 < (list_to_Z (UINT_MOD) (l_dp)))) (PreH13 : (shift_orig <= 0)) (PreH14 : (dn0 > 2)) (PreH15 : (dn0 <= nn0)) (PreH16 : (nn0 <= INT_MAX)) (PreH17 : (0 < d_orig)) (PreH18 : (0 <= shift_orig)) (PreH19 : (shift_orig < 32)) (PreH20 : ((Zlength (l_np)) = nn0)) (PreH21 : ((Zlength (l_dp)) = dn0)) (PreH22 : (list_within_bound UINT_MOD l_np )) (PreH23 : (list_within_bound UINT_MOD l_dp )) (PreH24 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH25 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH26 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH27 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH28 : (d1_orig <= UINT_MAX)) (PreH29 : (0 <= d0_orig)) (PreH30 : (d0_orig <= UINT_MAX)) (PreH31 : (0 <= di_orig)) (PreH32 : (di_orig <= UINT_MAX)) (PreH33 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH34 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d0_orig >= 0)) (PreH4 : (d1_orig >= 0)) (PreH5 : (shift_orig >= 0)) (PreH6 : (shift_orig <= 0)) (PreH7 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH8 : ((Zlength (l_rem_2)) = dn0)) (PreH9 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH10 : (list_within_bound UINT_MOD l_q_2 )) (PreH11 : (list_within_bound UINT_MOD l_rem_2 )) (PreH12 : (list_within_bound UINT_MOD l_tail_2 )) (PreH13 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH14 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH15 : (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) = ((qv_2 * (list_to_Z (UINT_MOD) (l_dp)) ) + rv_2 ))) (PreH16 : (0 <= rv_2)) (PreH17 : (rv_2 < (list_to_Z (UINT_MOD) (l_dp)))) (PreH18 : (shift_orig <= 0)) (PreH19 : (dn0 > 2)) (PreH20 : (dn0 <= nn0)) (PreH21 : (nn0 <= INT_MAX)) (PreH22 : (0 < d_orig)) (PreH23 : (0 <= shift_orig)) (PreH24 : (shift_orig < 32)) (PreH25 : ((Zlength (l_np)) = nn0)) (PreH26 : ((Zlength (l_dp)) = dn0)) (PreH27 : (list_within_bound UINT_MOD l_np )) (PreH28 : (list_within_bound UINT_MOD l_dp )) (PreH29 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH30 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH31 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH32 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH33 : (d1_orig <= UINT_MAX)) (PreH34 : (0 <= d0_orig)) (PreH35 : (d0_orig <= UINT_MAX)) (PreH36 : (0 <= di_orig)) (PreH37 : (di_orig <= UINT_MAX)) (PreH38 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH39 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (store_preinv_divisor dp0 inv0 dn0 d_orig )
).

Definition mpn_div_qr_preinv_partial_solve_wit_1_pure := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn0 = 1)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (inv0 = inv0) ” 
  &&  “ (nn0 > 0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_1_aux := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn0 = 1)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (inv0 = inv0) ” 
  &&  “ (nn0 > 0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (dn0 = 1) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  (optional_q_undef qp0 nn0 )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
.

Definition mpn_div_qr_preinv_partial_solve_wit_1 := mpn_div_qr_preinv_partial_solve_wit_1_pure -> mpn_div_qr_preinv_partial_solve_wit_1_aux.

Definition mpn_div_qr_preinv_partial_solve_wit_2 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (qv: Z) (l_q: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_q)) = nn0)) (PreH2 : (list_within_bound UINT_MOD l_q )) (PreH3 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH4 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + retval ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < d_orig)) (PreH7 : (dn0 = 1)) (PreH8 : (dn0 > 0)) (PreH9 : (dn0 <= nn0)) (PreH10 : (nn0 <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_full qp0 nn0 l_q )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
|--
  “ ((Zlength (l_q)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + retval )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < d_orig) ” 
  &&  “ (dn0 = 1) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  (((np0 + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0 0 0 nn0 l_np )
  **  (optional_q_full qp0 nn0 l_q )
  **  (store_div_inverse inv0 1 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 1 )
.

Definition mpn_div_qr_preinv_partial_solve_wit_3_pure := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn0 = 2)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 (nn0 - 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (inv0 = inv0) ” 
  &&  “ (nn0 >= 2) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_3_aux := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (dn0 = 2)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp0 (nn0 - 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (inv0 = inv0) ” 
  &&  “ (nn0 >= 2) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (dn0 = 2) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  (optional_q_undef qp0 (nn0 - 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_div_inverse inv0 2 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig 2 )
.

Definition mpn_div_qr_preinv_partial_solve_wit_3 := mpn_div_qr_preinv_partial_solve_wit_3_pure -> mpn_div_qr_preinv_partial_solve_wit_3_aux.

Definition mpn_div_qr_preinv_partial_solve_wit_4_pure := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : (0 < d_orig)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH13 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH14 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH15 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH16 : (d1_orig <= UINT_MAX)) (PreH17 : (0 <= d0_orig)) (PreH18 : (d0_orig <= UINT_MAX)) (PreH19 : (0 <= di_orig)) (PreH20 : (di_orig <= UINT_MAX)) (PreH21 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH22 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |->_)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (np0 = np0) ” 
  &&  “ (nn0 > 0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_4_aux := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : (0 < d_orig)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH13 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH14 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH15 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH16 : (d1_orig <= UINT_MAX)) (PreH17 : (0 <= d0_orig)) (PreH18 : (d0_orig <= UINT_MAX)) (PreH19 : (0 <= di_orig)) (PreH20 : (di_orig <= UINT_MAX)) (PreH21 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH22 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (np0 = np0) ” 
  &&  “ (nn0 > 0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ”
  &&  (UIntArray.full np0 nn0 l_np )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_preinv_partial_solve_wit_4 := mpn_div_qr_preinv_partial_solve_wit_4_pure -> mpn_div_qr_preinv_partial_solve_wit_4_aux.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (dn0 > 2)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : (0 < d_orig)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : ((Zlength (l_np)) = nn0)) (PreH12 : ((Zlength (l_dp)) = dn0)) (PreH13 : (list_within_bound UINT_MOD l_np )) (PreH14 : (list_within_bound UINT_MOD l_dp )) (PreH15 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH16 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH17 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH18 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH19 : (d1_orig <= UINT_MAX)) (PreH20 : (0 <= d0_orig)) (PreH21 : (d0_orig <= UINT_MAX)) (PreH22 : (0 <= di_orig)) (PreH23 : (di_orig <= UINT_MAX)) (PreH24 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH25 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (retval = retval) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_out)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) ((Zlength (l_out)))) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_out)) - (Zlength (l_dp)) ) + 1 ))) )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ”
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) ((Zlength (l_out)))) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_out)) - (Zlength (l_dp)) ) + 1 ))) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
).

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_1 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_2 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_3 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_4 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_5 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_6 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_7 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_8 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((retval * (Z.pow (UINT_MOD) ((Zlength (l_out)))) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_out)) - (Zlength (l_dp)) ) + 1 ))) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_9 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_10 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_11 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : ((Zlength (l_out)) = nn0)) (PreH12 : (list_within_bound UINT_MOD l_out )) (PreH13 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH14 : (shift_orig > 0)) (PreH15 : (dn0 > 2)) (PreH16 : (dn0 <= nn0)) (PreH17 : (nn0 <= INT_MAX)) (PreH18 : (0 < d_orig)) (PreH19 : (0 <= shift_orig)) (PreH20 : (shift_orig < 32)) (PreH21 : ((Zlength (l_np)) = nn0)) (PreH22 : ((Zlength (l_dp)) = dn0)) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_dp )) (PreH25 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH26 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH27 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH28 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH29 : (d1_orig <= UINT_MAX)) (PreH30 : (0 <= d0_orig)) (PreH31 : (d0_orig <= UINT_MAX)) (PreH32 : (0 <= di_orig)) (PreH33 : (di_orig <= UINT_MAX)) (PreH34 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH35 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> retval)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_5_aux := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (dn0 > 2)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : (0 < d_orig)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : ((Zlength (l_np)) = nn0)) (PreH12 : ((Zlength (l_dp)) = dn0)) (PreH13 : (list_within_bound UINT_MOD l_np )) (PreH14 : (list_within_bound UINT_MOD l_dp )) (PreH15 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH16 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH17 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH18 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH19 : (d1_orig <= UINT_MAX)) (PreH20 : (0 <= d0_orig)) (PreH21 : (d0_orig <= UINT_MAX)) (PreH22 : (0 <= di_orig)) (PreH23 : (di_orig <= UINT_MAX)) (PreH24 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH25 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (UIntArray.full np0 nn0 l_out )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (retval = retval) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_out)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ” 
  &&  “ (((retval * (Z.pow (UINT_MOD) ((Zlength (l_out)))) ) + (list_to_Z (UINT_MOD) (l_out)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_out)) - (Zlength (l_dp)) ) + 1 ))) )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ ((Zlength (l_out)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_out )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_preinv_partial_solve_wit_5 := mpn_div_qr_preinv_partial_solve_wit_5_pure -> mpn_div_qr_preinv_partial_solve_wit_5_aux.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure := 
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : (0 < d_orig)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH13 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH14 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH15 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH16 : (d1_orig <= UINT_MAX)) (PreH17 : (0 <= d0_orig)) (PreH18 : (d0_orig <= UINT_MAX)) (PreH19 : (0 <= di_orig)) (PreH20 : (di_orig <= UINT_MAX)) (PreH21 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH22 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((Zlength (l_np)))) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_np)) - (Zlength (l_dp)) ) + 1 ))) )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ” 
  &&  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ”
) \/
(
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((Zlength (l_np)))) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_np)) - (Zlength (l_dp)) ) + 1 ))) )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
).

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_1 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_2 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_3 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_4 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_5 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_6 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_7 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_8 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((0 * (Z.pow (UINT_MOD) ((Zlength (l_np)))) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_np)) - (Zlength (l_dp)) ) + 1 ))) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_9 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_10 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_11 := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (shift_orig <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (di_orig >= 0)) (PreH5 : (d0_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (shift_orig >= 0)) (PreH8 : (dn0 <= INT_MAX)) (PreH9 : (dn0 >= INT_MIN)) (PreH10 : (nn0 >= INT_MIN)) (PreH11 : (shift_orig <= 0)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : (0 < d_orig)) (PreH16 : (0 <= shift_orig)) (PreH17 : (shift_orig < 32)) (PreH18 : ((Zlength (l_np)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH23 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH24 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH26 : (d1_orig <= UINT_MAX)) (PreH27 : (0 <= d0_orig)) (PreH28 : (d0_orig <= UINT_MAX)) (PreH29 : (0 <= di_orig)) (PreH30 : (di_orig <= UINT_MAX)) (PreH31 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "nh" ) )) # UInt  |-> 0)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_6_aux := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : (0 < d_orig)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) ))) (PreH13 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH14 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH15 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH16 : (d1_orig <= UINT_MAX)) (PreH17 : (0 <= d0_orig)) (PreH18 : (d0_orig <= UINT_MAX)) (PreH19 : (0 <= di_orig)) (PreH20 : (di_orig <= UINT_MAX)) (PreH21 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH22 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth ((dn0 - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth ((dn0 - 1 )) (l_dp) (0)) ) + (Znth ((dn0 - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) (((nn0 - dn0 ) + 1 ))) )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((Zlength (l_np)))) ) + (list_to_Z (UINT_MOD) (l_np)) ) < ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (UINT_MOD) ((((Zlength (l_np)) - (Zlength (l_dp)) ) + 1 ))) )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) )) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) ) + (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (((Zlength (l_dp)) - 2 )) (l_dp) (0))) ” 
  &&  “ ((Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0)) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (((Zlength (l_dp)) - 1 )) (l_dp) (0))) ” 
  &&  “ (0 < (list_to_Z (UINT_MOD) (l_dp))) ” 
  &&  “ (shift_orig <= 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_preinv_partial_solve_wit_6 := mpn_div_qr_preinv_partial_solve_wit_6_pure -> mpn_div_qr_preinv_partial_solve_wit_6_aux.

Definition mpn_div_qr_preinv_partial_solve_wit_7_pure := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem: (@list Z)) (PreH1 : (dn0 > 2)) (PreH2 : (dn0 <= nn0)) (PreH3 : (nn0 <= INT_MAX)) (PreH4 : (0 < d_orig)) (PreH5 : (1 <= shift)) (PreH6 : (shift < 32)) (PreH7 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH8 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH17 : ((Zlength (l_np)) = nn0)) (PreH18 : ((Zlength (l_norm)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH21 : ((Zlength (l_rem)) = dn0)) (PreH22 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_norm )) (PreH25 : (list_within_bound UINT_MOD l_dp )) (PreH26 : (list_within_bound UINT_MOD l_q )) (PreH27 : (list_within_bound UINT_MOD l_rem )) (PreH28 : (list_within_bound UINT_MOD l_tail )) (PreH29 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH30 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH31 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH32 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH33 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH34 : (0 <= rv)) (PreH35 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "nh" ) )) # UInt  |-> nh_orig)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.full np0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (np0 = np0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ”
.

Definition mpn_div_qr_preinv_partial_solve_wit_7_aux := 
forall (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (inv0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (l_q: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (nh_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (shift: Z) (l_rem: (@list Z)) (PreH1 : (dn0 > 2)) (PreH2 : (dn0 <= nn0)) (PreH3 : (nn0 <= INT_MAX)) (PreH4 : (0 < d_orig)) (PreH5 : (1 <= shift)) (PreH6 : (shift < 32)) (PreH7 : (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0)))) (PreH8 : (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0)))) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH17 : ((Zlength (l_np)) = nn0)) (PreH18 : ((Zlength (l_norm)) = nn0)) (PreH19 : ((Zlength (l_dp)) = dn0)) (PreH20 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH21 : ((Zlength (l_rem)) = dn0)) (PreH22 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH23 : (list_within_bound UINT_MOD l_np )) (PreH24 : (list_within_bound UINT_MOD l_norm )) (PreH25 : (list_within_bound UINT_MOD l_dp )) (PreH26 : (list_within_bound UINT_MOD l_q )) (PreH27 : (list_within_bound UINT_MOD l_rem )) (PreH28 : (list_within_bound UINT_MOD l_tail )) (PreH29 : ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) ))) (PreH30 : (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) ))) (PreH31 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH32 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH33 : (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv ))) (PreH34 : (0 <= rv)) (PreH35 : (rv < (list_to_Z (UINT_MOD) (l_dp)))) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.full np0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (np0 = np0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ (0 < d_orig) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (d1_orig = (Znth ((dn0 - 1 )) (l_dp) (0))) ” 
  &&  “ (d0_orig = (Znth ((dn0 - 2 )) (l_dp) (0))) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_norm)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_norm ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = (d_orig * (Z.pow (2) (shift)) )) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_norm)) + (nh_orig * (Z.pow (UINT_MOD) (nn0)) ) ) = ((list_to_Z (UINT_MOD) (l_np)) * (Z.pow (2) (shift)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ (((nh_orig * (Z.pow (UINT_MOD) (nn0)) ) + (list_to_Z (UINT_MOD) (l_norm)) ) = ((qv * (list_to_Z (UINT_MOD) (l_dp)) ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < (list_to_Z (UINT_MOD) (l_dp))) ”
  &&  (UIntArray.full np0 dn0 l_rem )
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_preinv_partial_solve_wit_7 := mpn_div_qr_preinv_partial_solve_wit_7_pure -> mpn_div_qr_preinv_partial_solve_wit_7_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_preinv_safety_wit_1 : mpn_div_qr_preinv_safety_wit_1.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_2 : mpn_div_qr_preinv_safety_wit_2.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_3 : mpn_div_qr_preinv_safety_wit_3.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_4 : mpn_div_qr_preinv_safety_wit_4.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_5 : mpn_div_qr_preinv_safety_wit_5.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_6 : mpn_div_qr_preinv_safety_wit_6.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_7 : mpn_div_qr_preinv_safety_wit_7.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_8 : mpn_div_qr_preinv_safety_wit_8.
Axiom proof_of_mpn_div_qr_preinv_safety_wit_9 : mpn_div_qr_preinv_safety_wit_9.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_1 : mpn_div_qr_preinv_entail_wit_1.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_2 : mpn_div_qr_preinv_entail_wit_2.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_3 : mpn_div_qr_preinv_entail_wit_3.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_4 : mpn_div_qr_preinv_entail_wit_4.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_5 : mpn_div_qr_preinv_entail_wit_5.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_6 : mpn_div_qr_preinv_entail_wit_6.
Axiom proof_of_mpn_div_qr_preinv_entail_wit_7 : mpn_div_qr_preinv_entail_wit_7.
Axiom proof_of_mpn_div_qr_preinv_return_wit_1 : mpn_div_qr_preinv_return_wit_1.
Axiom proof_of_mpn_div_qr_preinv_return_wit_2 : mpn_div_qr_preinv_return_wit_2.
Axiom proof_of_mpn_div_qr_preinv_return_wit_3 : mpn_div_qr_preinv_return_wit_3.
Axiom proof_of_mpn_div_qr_preinv_return_wit_4 : mpn_div_qr_preinv_return_wit_4.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_1_pure : mpn_div_qr_preinv_partial_solve_wit_1_pure.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_1 : mpn_div_qr_preinv_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_2 : mpn_div_qr_preinv_partial_solve_wit_2.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_3_pure : mpn_div_qr_preinv_partial_solve_wit_3_pure.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_3 : mpn_div_qr_preinv_partial_solve_wit_3.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_4_pure : mpn_div_qr_preinv_partial_solve_wit_4_pure.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_4 : mpn_div_qr_preinv_partial_solve_wit_4.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure : mpn_div_qr_preinv_partial_solve_wit_5_pure.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_5 : mpn_div_qr_preinv_partial_solve_wit_5.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure : mpn_div_qr_preinv_partial_solve_wit_6_pure.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_6 : mpn_div_qr_preinv_partial_solve_wit_6.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_7_pure : mpn_div_qr_preinv_partial_solve_wit_7_pure.
Axiom proof_of_mpn_div_qr_preinv_partial_solve_wit_7 : mpn_div_qr_preinv_partial_solve_wit_7.

End VC_Correct.
