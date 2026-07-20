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

(*----- Function mpn_div_qr_2_preinv -----*)

Definition mpn_div_qr_2_preinv_safety_wit_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare >= 2)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH15 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH16 : (list_within_bound UINT_MOD l_np_bare )) (PreH17 : (qp0_bare <> 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare >= 2)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH15 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH16 : (list_within_bound UINT_MOD l_np_bare )) (PreH17 : (qp0_bare = 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_5 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_6 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_7 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_8 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_9 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_10 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_11 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_12 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_13 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_out 0))
|--
  “ ((nn0_bare - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 2 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_14 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_out 0))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_15 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_out 0))
|--
  “ ((nn0_bare - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 2 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_16 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> retval)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_out 0))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_17 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_np_bare 0))
|--
  “ ((nn0_bare - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 2 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_18 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_np_bare 0))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_19 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_np_bare 0))
|--
  “ ((nn0_bare - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 2 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_20 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |-> 0)
  **  ((( &( "r0" ) )) # UInt  |-> (Znth (nn0_bare - 1 ) l_np_bare 0))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_21 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH3 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH4 : (d1_orig <= UINT_MAX)) (PreH5 : (0 <= d0_orig)) (PreH6 : (d0_orig <= UINT_MAX)) (PreH7 : (0 <= di_orig)) (PreH8 : (di_orig <= UINT_MAX)) (PreH9 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH10 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH11 : (0 <= shift_orig)) (PreH12 : (shift_orig < 32)) (PreH13 : (nn0_bare >= 2)) (PreH14 : (nn0_bare <= INT_MAX)) (PreH15 : ((-1) <= i)) (PreH16 : (i <= (nn0_bare - 2 ))) (PreH17 : ((Zlength (l_cur)) = nn0_bare)) (PreH18 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH19 : (list_within_bound UINT_MOD l_cur )) (PreH20 : (list_within_bound UINT_MOD l_done )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH22 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH23 : (0 <= carry)) (PreH24 : (carry <= UINT_MAX)) (PreH25 : (0 <= r1)) (PreH26 : (r1 <= UINT_MAX)) (PreH27 : (0 <= r0)) (PreH28 : (r0 <= UINT_MAX)) (PreH29 : (0 <= remv)) (PreH30 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH31 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH32 : (shift_orig = 0)) (PreH33 : (carry = 0)) (PreH34 : (l_cur = l_np_bare)) (PreH35 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_22 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH3 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH4 : (d1_orig <= UINT_MAX)) (PreH5 : (0 <= d0_orig)) (PreH6 : (d0_orig <= UINT_MAX)) (PreH7 : (0 <= di_orig)) (PreH8 : (di_orig <= UINT_MAX)) (PreH9 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH10 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH11 : (0 <= shift_orig)) (PreH12 : (shift_orig < 32)) (PreH13 : (nn0_bare >= 2)) (PreH14 : (nn0_bare <= INT_MAX)) (PreH15 : ((-1) <= i)) (PreH16 : (i <= (nn0_bare - 2 ))) (PreH17 : ((Zlength (l_cur)) = nn0_bare)) (PreH18 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH19 : (list_within_bound UINT_MOD l_cur )) (PreH20 : (list_within_bound UINT_MOD l_done )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH22 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH23 : (0 <= carry)) (PreH24 : (carry <= UINT_MAX)) (PreH25 : (0 <= r1)) (PreH26 : (r1 <= UINT_MAX)) (PreH27 : (0 <= r0)) (PreH28 : (r0 <= UINT_MAX)) (PreH29 : (0 <= remv)) (PreH30 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH31 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH32 : (shift_orig = 0)) (PreH33 : (carry = 0)) (PreH34 : (l_cur = l_np_bare)) (PreH35 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_23 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH3 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH4 : (d1_orig <= UINT_MAX)) (PreH5 : (0 <= d0_orig)) (PreH6 : (d0_orig <= UINT_MAX)) (PreH7 : (0 <= di_orig)) (PreH8 : (di_orig <= UINT_MAX)) (PreH9 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH10 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH11 : (0 <= shift_orig)) (PreH12 : (shift_orig < 32)) (PreH13 : (nn0_bare >= 2)) (PreH14 : (nn0_bare <= INT_MAX)) (PreH15 : ((-1) <= i)) (PreH16 : (i <= (nn0_bare - 2 ))) (PreH17 : ((Zlength (l_cur)) = nn0_bare)) (PreH18 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH19 : (list_within_bound UINT_MOD l_cur )) (PreH20 : (list_within_bound UINT_MOD l_done )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH22 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH23 : (0 <= carry)) (PreH24 : (carry <= UINT_MAX)) (PreH25 : (0 <= r1)) (PreH26 : (r1 <= UINT_MAX)) (PreH27 : (0 <= r0)) (PreH28 : (r0 <= UINT_MAX)) (PreH29 : (0 <= remv)) (PreH30 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH31 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH32 : (shift_orig > 0)) (PreH33 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH34 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_24 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH3 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH4 : (d1_orig <= UINT_MAX)) (PreH5 : (0 <= d0_orig)) (PreH6 : (d0_orig <= UINT_MAX)) (PreH7 : (0 <= di_orig)) (PreH8 : (di_orig <= UINT_MAX)) (PreH9 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH10 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH11 : (0 <= shift_orig)) (PreH12 : (shift_orig < 32)) (PreH13 : (nn0_bare >= 2)) (PreH14 : (nn0_bare <= INT_MAX)) (PreH15 : ((-1) <= i)) (PreH16 : (i <= (nn0_bare - 2 ))) (PreH17 : ((Zlength (l_cur)) = nn0_bare)) (PreH18 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH19 : (list_within_bound UINT_MOD l_cur )) (PreH20 : (list_within_bound UINT_MOD l_done )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH22 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH23 : (0 <= carry)) (PreH24 : (carry <= UINT_MAX)) (PreH25 : (0 <= r1)) (PreH26 : (r1 <= UINT_MAX)) (PreH27 : (0 <= r0)) (PreH28 : (r0 <= UINT_MAX)) (PreH29 : (0 <= remv)) (PreH30 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH31 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH32 : (shift_orig > 0)) (PreH33 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH34 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_25 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_26 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_27 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare <> 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_28 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare <> 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_29 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare <> 0)) ,
  (UIntArray.undef_seg qp0_bare 0 i )
  **  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_30 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare <> 0)) ,
  (UIntArray.undef_seg qp0_bare 0 i )
  **  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_31 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare <> 0)) ,
  (UIntArray.undef_seg qp0_bare 0 i )
  **  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_32 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare <> 0)) ,
  (UIntArray.undef_seg qp0_bare 0 i )
  **  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_33 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_34 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_35 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_36 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r1" ) )) # UInt  |-> rv1)
  **  ((( &( "r0" ) )) # UInt  |-> rv0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_37 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_38 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_39 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_40 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_41 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_42 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_43 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_44 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_2_preinv_safety_wit_45 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((32 - shift_orig ) <= 31) ” 
  &&  “ (0 <= (32 - shift_orig )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_46 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_47 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_48 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((32 - shift_orig ) <= 31) ” 
  &&  “ (0 <= (32 - shift_orig )) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_49 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_50 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_51 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> (Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32))))
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_52 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> (Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32))))
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_53 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> (Z.shiftr r1 shift_orig))
  **  ((( &( "r0" ) )) # UInt  |-> (Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32))))
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_54 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> (Z.shiftr r1 shift_orig))
  **  ((( &( "r0" ) )) # UInt  |-> (Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32))))
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_55 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare = 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_56 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare <> 0)) ,
  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_57 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)) )
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> (Z.shiftr r1 shift_orig))
  **  ((( &( "r0" ) )) # UInt  |-> (Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32))))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_58 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)) )
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> (Z.shiftr r1 shift_orig))
  **  ((( &( "r0" ) )) # UInt  |-> (Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32))))
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_59 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) (r1) (l_cur)) )
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_safety_wit_60 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) (r1) (l_cur)) )
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_preinv_entail_wit_1_1 := 
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre >= 2)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre <> 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.undef_full qp_pre (nn_pre - 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 2 d_orig_bare )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre >= 2)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre <> 0)) ,
  (UIntArray.undef_full qp_pre (nn_pre - 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 2 d_orig_bare )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (inv_pre = inv0_bare) ” 
  &&  “ (nn_pre = nn0_bare) ” 
  &&  “ (np_pre = np0_bare) ” 
  &&  “ (qp_pre = qp0_bare) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
).

Definition mpn_div_qr_2_preinv_entail_wit_1_2 := 
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre >= 2)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 2 d_orig_bare )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre >= 2)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre = 0)) ,
  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 2 d_orig_bare )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (inv_pre = inv0_bare) ” 
  &&  “ (nn_pre = nn0_bare) ” 
  &&  “ (np_pre = np0_bare) ” 
  &&  “ (qp_pre = qp0_bare) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
).

Definition mpn_div_qr_2_preinv_entail_wit_2_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_out 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_out 0) <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 ((nn0_bare - 2 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 2 ) + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
|--
  EX (carry: Z)  (l_done: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_out)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_out 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_out 0) <= UINT_MAX) ” 
  &&  “ (0 <= ((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) )) ” 
  &&  “ (((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_out)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) ) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.undef_seg qp0_bare 0 ((nn0_bare - 2 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 2 ) + 1 ) (nn0_bare - 1 ) l_done )
).

Definition mpn_div_qr_2_preinv_entail_wit_2_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_out 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_out 0) <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  TT && emp 
|--
  EX (carry: Z)  (l_done: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_out)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_out 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_out 0) <= UINT_MAX) ” 
  &&  “ (0 <= ((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) )) ” 
  &&  “ (((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_out)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((retval * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_out 0) ) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  emp
).

Definition mpn_div_qr_2_preinv_entail_wit_2_3 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_np_bare 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 ((nn0_bare - 2 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 2 ) + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
|--
  EX (l_done: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_np_bare 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= ((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) )) ” 
  &&  “ (((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_np_bare)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) ) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.undef_seg qp0_bare 0 ((nn0_bare - 2 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 2 ) + 1 ) (nn0_bare - 1 ) l_done )
).

Definition mpn_div_qr_2_preinv_entail_wit_2_4 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_np_bare 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  TT && emp 
|--
  EX (l_done: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (nn0_bare - 2 )) ” 
  &&  “ ((nn0_bare - 2 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (nn0_bare - 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn0_bare - 1 ) l_np_bare 0)) ” 
  &&  “ ((Znth (nn0_bare - 1 ) l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= ((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) )) ” 
  &&  “ (((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((nn0_bare - ((nn0_bare - 2 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((nn0_bare - 2 ) + 1 )) (nn0_bare) (l_np_bare)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((0 * UINT_MOD ) + (Znth (nn0_bare - 1 ) l_np_bare 0) ) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  emp
).

Definition mpn_div_qr_2_preinv_entail_wit_3_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_entail_wit_3_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_3: Z) (remv_3: Z) (r0_3: Z) (r1_3: Z) (qv_done_3: Z) (l_done_3: (@list Z)) (l_cur_3: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1_3 * (Z.pow (UINT_MOD) (2)) ) + (r0_3 * UINT_MOD ) ) + (Znth i l_cur_3 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_3)) = nn0_bare)) (PreH27 : ((Zlength (l_done_3)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_3 )) (PreH29 : (list_within_bound UINT_MOD l_done_3 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_3)) = qv_done_3)) (PreH31 : (((r1_3 * UINT_MOD ) + r0_3 ) = remv_3)) (PreH32 : (0 <= carry_3)) (PreH33 : (carry_3 <= UINT_MAX)) (PreH34 : (0 <= r1_3)) (PreH35 : (r1_3 <= UINT_MAX)) (PreH36 : (0 <= r0_3)) (PreH37 : (r0_3 <= UINT_MAX)) (PreH38 : (0 <= remv_3)) (PreH39 : (remv_3 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_3 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_3)))) ) = ((qv_done_3 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_3 ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry_3 = 0)) (PreH43 : (l_cur_3 = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_3 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_3 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_3 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (carry: Z)  (remv: Z)  (r0: Z)  (r1: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (carry_2: Z)  (remv_2: Z)  (r0_2: Z)  (r1_2: Z)  (qv_done_2: Z)  (l_done_2: (@list Z))  (l_cur_2: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2) ” 
  &&  “ (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= UINT_MAX) ” 
  &&  “ (0 <= r1_2) ” 
  &&  “ (r1_2 <= UINT_MAX) ” 
  &&  “ (0 <= r0_2) ” 
  &&  “ (r0_2 <= UINT_MAX) ” 
  &&  “ (0 <= remv_2) ” 
  &&  “ (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_2_preinv_entail_wit_3_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0_2: Z) (r1_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1_2)) (PreH35 : (r1_2 <= UINT_MAX)) (PreH36 : (0 <= r0_2)) (PreH37 : (r0_2 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2) ” 
  &&  “ (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= UINT_MAX) ” 
  &&  “ (0 <= r1_2) ” 
  &&  “ (r1_2 <= UINT_MAX) ” 
  &&  “ (0 <= r0_2) ” 
  &&  “ (r0_2 <= UINT_MAX) ” 
  &&  “ (0 <= remv_2) ” 
  &&  “ (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_entail_wit_3_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_3: Z) (remv_3: Z) (r0_3: Z) (r1_3: Z) (qv_done_3: Z) (l_done_3: (@list Z)) (l_cur_3: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1_3 * (Z.pow (UINT_MOD) (2)) ) + (r0_3 * UINT_MOD ) ) + (Znth i l_cur_3 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_3)) = nn0_bare)) (PreH27 : ((Zlength (l_done_3)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_3 )) (PreH29 : (list_within_bound UINT_MOD l_done_3 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_3)) = qv_done_3)) (PreH31 : (((r1_3 * UINT_MOD ) + r0_3 ) = remv_3)) (PreH32 : (0 <= carry_3)) (PreH33 : (carry_3 <= UINT_MAX)) (PreH34 : (0 <= r1_3)) (PreH35 : (r1_3 <= UINT_MAX)) (PreH36 : (0 <= r0_3)) (PreH37 : (r0_3 <= UINT_MAX)) (PreH38 : (0 <= remv_3)) (PreH39 : (remv_3 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_3 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_3)))) ) = ((qv_done_3 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_3 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_3)) + (carry_3 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_3 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_3 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_3 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (carry: Z)  (remv: Z)  (r0: Z)  (r1: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (carry_2: Z)  (remv_2: Z)  (r0_2: Z)  (r1_2: Z)  (qv_done_2: Z)  (l_done_2: (@list Z))  (l_cur_2: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2) ” 
  &&  “ (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= UINT_MAX) ” 
  &&  “ (0 <= r1_2) ” 
  &&  “ (r1_2 <= UINT_MAX) ” 
  &&  “ (0 <= r0_2) ” 
  &&  “ (r0_2 <= UINT_MAX) ” 
  &&  “ (0 <= remv_2) ” 
  &&  “ (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_2_preinv_entail_wit_4_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_3: Z) (remv_3: Z) (r0_3: Z) (r1_3: Z) (qv_done_3: Z) (l_done_3: (@list Z)) (l_cur_3: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1_3 * (Z.pow (UINT_MOD) (2)) ) + (r0_3 * UINT_MOD ) ) + (Znth i l_cur_3 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_3)) = nn0_bare)) (PreH27 : ((Zlength (l_done_3)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_3 )) (PreH29 : (list_within_bound UINT_MOD l_done_3 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_3)) = qv_done_3)) (PreH31 : (((r1_3 * UINT_MOD ) + r0_3 ) = remv_3)) (PreH32 : (0 <= carry_3)) (PreH33 : (carry_3 <= UINT_MAX)) (PreH34 : (0 <= r1_3)) (PreH35 : (r1_3 <= UINT_MAX)) (PreH36 : (0 <= r0_3)) (PreH37 : (r0_3 <= UINT_MAX)) (PreH38 : (0 <= remv_3)) (PreH39 : (remv_3 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_3 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_3)))) ) = ((qv_done_3 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_3 ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry_3 = 0)) (PreH43 : (l_cur_3 = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_3 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_3 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (carry: Z)  (remv: Z)  (r0: Z)  (r1: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (carry_2: Z)  (remv_2: Z)  (r0_2: Z)  (r1_2: Z)  (qv_done_2: Z)  (l_done_2: (@list Z))  (l_cur_2: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2) ” 
  &&  “ (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= UINT_MAX) ” 
  &&  “ (0 <= r1_2) ” 
  &&  “ (r1_2 <= UINT_MAX) ” 
  &&  “ (0 <= r0_2) ” 
  &&  “ (r0_2 <= UINT_MAX) ” 
  &&  “ (0 <= remv_2) ” 
  &&  “ (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_2_preinv_entail_wit_4_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_entail_wit_4_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_3: Z) (remv_3: Z) (r0_3: Z) (r1_3: Z) (qv_done_3: Z) (l_done_3: (@list Z)) (l_cur_3: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1_3 * (Z.pow (UINT_MOD) (2)) ) + (r0_3 * UINT_MOD ) ) + (Znth i l_cur_3 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_3)) = nn0_bare)) (PreH27 : ((Zlength (l_done_3)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_3 )) (PreH29 : (list_within_bound UINT_MOD l_done_3 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_3)) = qv_done_3)) (PreH31 : (((r1_3 * UINT_MOD ) + r0_3 ) = remv_3)) (PreH32 : (0 <= carry_3)) (PreH33 : (carry_3 <= UINT_MAX)) (PreH34 : (0 <= r1_3)) (PreH35 : (r1_3 <= UINT_MAX)) (PreH36 : (0 <= r0_3)) (PreH37 : (r0_3 <= UINT_MAX)) (PreH38 : (0 <= remv_3)) (PreH39 : (remv_3 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_3 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_3)))) ) = ((qv_done_3 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_3 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_3)) + (carry_3 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_3 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_3 0))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (carry: Z)  (remv: Z)  (r0: Z)  (r1: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (carry_2: Z)  (remv_2: Z)  (r0_2: Z)  (r1_2: Z)  (qv_done_2: Z)  (l_done_2: (@list Z))  (l_cur_2: (@list Z)) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2) ” 
  &&  “ (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= UINT_MAX) ” 
  &&  “ (0 <= r1_2) ” 
  &&  “ (r1_2 <= UINT_MAX) ” 
  &&  “ (0 <= r0_2) ” 
  &&  “ (r0_2 <= UINT_MAX) ” 
  &&  “ (0 <= remv_2) ” 
  &&  “ (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_2_preinv_entail_wit_4_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0_2: Z) (r1_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1_2)) (PreH35 : (r1_2 <= UINT_MAX)) (PreH36 : (0 <= r0_2)) (PreH37 : (r0_2 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1_2 * (Z.pow (UINT_MOD) (2)) ) + (r0_2 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2) ” 
  &&  “ (((r1_2 * UINT_MOD ) + r0_2 ) = remv_2) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= UINT_MAX) ” 
  &&  “ (0 <= r1_2) ” 
  &&  “ (r1_2 <= UINT_MAX) ” 
  &&  “ (0 <= r0_2) ” 
  &&  “ (r0_2 <= UINT_MAX) ” 
  &&  “ (0 <= remv_2) ” 
  &&  “ (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur_2 0))
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_entail_wit_5_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry_2 = 0)) (PreH43 : (l_cur_2 = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare <> 0)) ,
  (UIntArray.undef_seg qp0_bare 0 i )
  **  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 ((i - 1 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((i - 1 ) + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (qv >= 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv1)) (PreH5 : (rv1 <= UINT_MAX)) (PreH6 : (0 <= rv0)) (PreH7 : (rv0 <= UINT_MAX)) (PreH8 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH9 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH10 : (i >= 0)) (PreH11 : (0 < d_orig_bare)) (PreH12 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH21 : (0 <= shift_orig)) (PreH22 : (shift_orig < 32)) (PreH23 : (nn0_bare >= 2)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((-1) <= i)) (PreH26 : (i <= (nn0_bare - 2 ))) (PreH27 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH28 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH33 : (0 <= carry_2)) (PreH34 : (carry_2 <= UINT_MAX)) (PreH35 : (0 <= r1)) (PreH36 : (r1 <= UINT_MAX)) (PreH37 : (0 <= r0)) (PreH38 : (r0 <= UINT_MAX)) (PreH39 : (0 <= remv_2)) (PreH40 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH41 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH42 : (shift_orig = 0)) (PreH43 : (carry_2 = 0)) (PreH44 : (l_cur_2 = l_np_bare)) (PreH45 : (qp0_bare <> 0)) (PreH46 : (qp0_bare <> 0)) ,
  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (l_cur_2 = l_np_bare) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= ((rv1 * UINT_MOD ) + rv0 )) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_np_bare)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((rv1 * UINT_MOD ) + rv0 ) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.seg qp0_bare ((i - 1 ) + 1 ) (nn0_bare - 1 ) l_done )
).

Definition mpn_div_qr_2_preinv_entail_wit_5_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare <> 0)) ,
  (UIntArray.undef_seg qp0_bare 0 i )
  **  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 ((i - 1 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((i - 1 ) + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (qv >= 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv1)) (PreH5 : (rv1 <= UINT_MAX)) (PreH6 : (0 <= rv0)) (PreH7 : (rv0 <= UINT_MAX)) (PreH8 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH9 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH10 : (i >= 0)) (PreH11 : (0 < d_orig_bare)) (PreH12 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH21 : (0 <= shift_orig)) (PreH22 : (shift_orig < 32)) (PreH23 : (nn0_bare >= 2)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((-1) <= i)) (PreH26 : (i <= (nn0_bare - 2 ))) (PreH27 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH28 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH33 : (0 <= carry_2)) (PreH34 : (carry_2 <= UINT_MAX)) (PreH35 : (0 <= r1)) (PreH36 : (r1 <= UINT_MAX)) (PreH37 : (0 <= r0)) (PreH38 : (r0 <= UINT_MAX)) (PreH39 : (0 <= remv_2)) (PreH40 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH41 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH42 : (shift_orig > 0)) (PreH43 : (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare <> 0)) ,
  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |-> qv)
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done_2 )
|--
  EX (carry: Z)  (l_done: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= ((rv1 * UINT_MOD ) + rv0 )) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_cur_2)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((rv1 * UINT_MOD ) + rv0 ) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.seg qp0_bare ((i - 1 ) + 1 ) (nn0_bare - 1 ) l_done )
).

Definition mpn_div_qr_2_preinv_entail_wit_5_3 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry_2 = 0)) (PreH43 : (l_cur_2 = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry_2 = 0)) (PreH43 : (l_cur_2 = l_np_bare)) (PreH44 : (qp0_bare = 0)) (PreH45 : (qp0_bare = 0)) ,
  TT && emp 
|--
  EX (l_done: (@list Z)) ,
  “ (l_cur_2 = l_np_bare) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= ((rv1 * UINT_MOD ) + rv0 )) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_np_bare)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((rv1 * UINT_MOD ) + rv0 ) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  emp
).

Definition mpn_div_qr_2_preinv_entail_wit_5_4 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (remv: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (carry_2: Z) (remv_2: Z) (r0: Z) (r1: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur_2 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur_2 )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv_2)) (PreH39 : (remv_2 < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur_2)))) ) = ((qv_done_2 * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv_2 ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare = 0)) (PreH44 : (qp0_bare = 0)) ,
  TT && emp 
|--
  EX (carry: Z)  (l_done: (@list Z)) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur_2)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - (i - 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (0 <= ((rv1 * UINT_MOD ) + rv0 )) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - ((i - 1 ) + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (nn0_bare) (l_cur_2)))) ) = (((list_to_Z (UINT_MOD) (l_done)) * ((d1_orig * UINT_MOD ) + d0_orig ) ) + ((rv1 * UINT_MOD ) + rv0 ) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur_2)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  emp
).

Definition mpn_div_qr_2_preinv_return_wit_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) ((Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32)))) ((replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)))) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d0_orig >= 0)) (PreH4 : (d1_orig >= 0)) (PreH5 : (shift_orig >= 0)) (PreH6 : (shift_orig > 0)) (PreH7 : (i < 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH18 : (0 <= shift_orig)) (PreH19 : (shift_orig < 32)) (PreH20 : (nn0_bare >= 2)) (PreH21 : (nn0_bare <= INT_MAX)) (PreH22 : ((-1) <= i)) (PreH23 : (i <= (nn0_bare - 2 ))) (PreH24 : ((Zlength (l_cur)) = nn0_bare)) (PreH25 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH26 : (list_within_bound UINT_MOD l_cur )) (PreH27 : (list_within_bound UINT_MOD l_done )) (PreH28 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH29 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH30 : (0 <= carry)) (PreH31 : (carry <= UINT_MAX)) (PreH32 : (0 <= r1)) (PreH33 : (r1 <= UINT_MAX)) (PreH34 : (0 <= r0)) (PreH35 : (r0 <= UINT_MAX)) (PreH36 : (0 <= remv)) (PreH37 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH38 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH39 : (shift_orig > 0)) (PreH40 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH41 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) ((Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32)))) ((replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)))) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig_bare ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
).

Definition mpn_div_qr_2_preinv_return_wit_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) ((Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32)))) ((replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)))) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare (nn0_bare - 1 ) l_q )
  **  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d0_orig >= 0)) (PreH4 : (d1_orig >= 0)) (PreH5 : (shift_orig >= 0)) (PreH6 : (shift_orig > 0)) (PreH7 : (i < 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH18 : (0 <= shift_orig)) (PreH19 : (shift_orig < 32)) (PreH20 : (nn0_bare >= 2)) (PreH21 : (nn0_bare <= INT_MAX)) (PreH22 : ((-1) <= i)) (PreH23 : (i <= (nn0_bare - 2 ))) (PreH24 : ((Zlength (l_cur)) = nn0_bare)) (PreH25 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH26 : (list_within_bound UINT_MOD l_cur )) (PreH27 : (list_within_bound UINT_MOD l_done )) (PreH28 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH29 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH30 : (0 <= carry)) (PreH31 : (carry <= UINT_MAX)) (PreH32 : (0 <= r1)) (PreH33 : (r1 <= UINT_MAX)) (PreH34 : (0 <= r0)) (PreH35 : (r0 <= UINT_MAX)) (PreH36 : (0 <= remv)) (PreH37 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH38 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH39 : (shift_orig > 0)) (PreH40 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH41 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) ((Z.lor (Z.shiftr r0 shift_orig) (unsigned_last_nbits ((Z.shiftl r1 (32 - shift_orig ))) (32)))) ((replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)))) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig_bare ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare (nn0_bare - 1 ) l_q )
  **  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
).

Definition mpn_div_qr_2_preinv_return_wit_3 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) (r0) ((replace_Znth (1) (r1) (l_cur)))) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d0_orig >= 0)) (PreH4 : (d1_orig >= 0)) (PreH5 : (shift_orig >= 0)) (PreH6 : (shift_orig <= 0)) (PreH7 : (i < 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH18 : (0 <= shift_orig)) (PreH19 : (shift_orig < 32)) (PreH20 : (nn0_bare >= 2)) (PreH21 : (nn0_bare <= INT_MAX)) (PreH22 : ((-1) <= i)) (PreH23 : (i <= (nn0_bare - 2 ))) (PreH24 : ((Zlength (l_cur)) = nn0_bare)) (PreH25 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH26 : (list_within_bound UINT_MOD l_cur )) (PreH27 : (list_within_bound UINT_MOD l_done )) (PreH28 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH29 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH30 : (0 <= carry)) (PreH31 : (carry <= UINT_MAX)) (PreH32 : (0 <= r1)) (PreH33 : (r1 <= UINT_MAX)) (PreH34 : (0 <= r0)) (PreH35 : (r0 <= UINT_MAX)) (PreH36 : (0 <= remv)) (PreH37 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH38 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH39 : (shift_orig = 0)) (PreH40 : (carry = 0)) (PreH41 : (l_cur = l_np_bare)) (PreH42 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) (r0) ((replace_Znth (1) (r1) (l_cur)))) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig_bare ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
).

Definition mpn_div_qr_2_preinv_return_wit_4 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) (r0) ((replace_Znth (1) (r1) (l_cur)))) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare (nn0_bare - 1 ) l_q )
  **  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d0_orig >= 0)) (PreH4 : (d1_orig >= 0)) (PreH5 : (shift_orig >= 0)) (PreH6 : (shift_orig <= 0)) (PreH7 : (i < 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH18 : (0 <= shift_orig)) (PreH19 : (shift_orig < 32)) (PreH20 : (nn0_bare >= 2)) (PreH21 : (nn0_bare <= INT_MAX)) (PreH22 : ((-1) <= i)) (PreH23 : (i <= (nn0_bare - 2 ))) (PreH24 : ((Zlength (l_cur)) = nn0_bare)) (PreH25 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH26 : (list_within_bound UINT_MOD l_cur )) (PreH27 : (list_within_bound UINT_MOD l_done )) (PreH28 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH29 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH30 : (0 <= carry)) (PreH31 : (carry <= UINT_MAX)) (PreH32 : (0 <= r1)) (PreH33 : (r1 <= UINT_MAX)) (PreH34 : (0 <= r0)) (PreH35 : (r0 <= UINT_MAX)) (PreH36 : (0 <= remv)) (PreH37 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH38 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH39 : (shift_orig = 0)) (PreH40 : (carry = 0)) (PreH41 : (l_cur = l_np_bare)) (PreH42 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (0) (r0) ((replace_Znth (1) (r1) (l_cur)))) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig_bare ) + (list_to_Z (UINT_MOD) (l_rem)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare (nn0_bare - 1 ) l_q )
  **  (UIntArray.seg np0_bare 0 2 l_rem )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )
).

Definition mpn_div_qr_2_preinv_partial_solve_wit_1_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (np0_bare = np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ”
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_1_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (np0_bare = np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_1 := mpn_div_qr_2_preinv_partial_solve_wit_1_pure -> mpn_div_qr_2_preinv_partial_solve_wit_1_aux.

Definition mpn_div_qr_2_preinv_partial_solve_wit_2_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
|--
  “ (np0_bare = np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ”
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_2_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (np0_bare = np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_2 := mpn_div_qr_2_preinv_partial_solve_wit_2_pure -> mpn_div_qr_2_preinv_partial_solve_wit_2_aux.

Definition mpn_div_qr_2_preinv_partial_solve_wit_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Zlength (l_out)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + ((nn0_bare - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (nn0_bare - 1 ) l_out 0))
  **  (UIntArray.missing_i np0_bare (nn0_bare - 1 ) 0 nn0_bare l_out )
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (shift_orig > 0)) (PreH5 : (nn0_bare >= 2)) (PreH6 : (nn0_bare <= INT_MAX)) (PreH7 : (0 <= shift_orig)) (PreH8 : (shift_orig < 32)) (PreH9 : (0 < d_orig_bare)) (PreH10 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_out )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Zlength (l_out)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + ((nn0_bare - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (nn0_bare - 1 ) l_out 0))
  **  (UIntArray.missing_i np0_bare (nn0_bare - 1 ) 0 nn0_bare l_out )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_5 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) ,
  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 0) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + ((nn0_bare - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (nn0_bare - 1 ) l_np_bare 0))
  **  (UIntArray.missing_i np0_bare (nn0_bare - 1 ) 0 nn0_bare l_np_bare )
  **  (UIntArray.undef_full qp0_bare (nn0_bare - 1 ) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_6 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare >= 2)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (0 < d_orig_bare)) (PreH7 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 0) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + ((nn0_bare - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (nn0_bare - 1 ) l_np_bare 0))
  **  (UIntArray.missing_i np0_bare (nn0_bare - 1 ) 0 nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_7 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.missing_i np0_bare i 0 nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_8 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.missing_i np0_bare i 0 nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_9 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.missing_i np0_bare i 0 nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_10 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_cur 0))
  **  (UIntArray.missing_i np0_bare i 0 nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_11_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ”
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_11_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_11 := mpn_div_qr_2_preinv_partial_solve_wit_11_pure -> mpn_div_qr_2_preinv_partial_solve_wit_11_aux.

Definition mpn_div_qr_2_preinv_partial_solve_wit_12_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ”
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_12_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig = 0)) (PreH34 : (carry = 0)) (PreH35 : (l_cur = l_np_bare)) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_12 := mpn_div_qr_2_preinv_partial_solve_wit_12_pure -> mpn_div_qr_2_preinv_partial_solve_wit_12_aux.

Definition mpn_div_qr_2_preinv_partial_solve_wit_13_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ”
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_13_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_13 := mpn_div_qr_2_preinv_partial_solve_wit_13_pure -> mpn_div_qr_2_preinv_partial_solve_wit_13_aux.

Definition mpn_div_qr_2_preinv_partial_solve_wit_14_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "n0" ) )) # UInt  |-> (Znth i l_cur 0))
  **  ((( &( "shift" ) )) # UInt  |-> shift_orig)
  **  ((( &( "d1" ) )) # UInt  |-> d1_orig)
  **  ((( &( "d0" ) )) # UInt  |-> d0_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ”
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_14_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (i >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH4 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH5 : (d1_orig <= UINT_MAX)) (PreH6 : (0 <= d0_orig)) (PreH7 : (d0_orig <= UINT_MAX)) (PreH8 : (0 <= di_orig)) (PreH9 : (di_orig <= UINT_MAX)) (PreH10 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (nn0_bare >= 2)) (PreH15 : (nn0_bare <= INT_MAX)) (PreH16 : ((-1) <= i)) (PreH17 : (i <= (nn0_bare - 2 ))) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH20 : (list_within_bound UINT_MOD l_cur )) (PreH21 : (list_within_bound UINT_MOD l_done )) (PreH22 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH23 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH24 : (0 <= carry)) (PreH25 : (carry <= UINT_MAX)) (PreH26 : (0 <= r1)) (PreH27 : (r1 <= UINT_MAX)) (PreH28 : (0 <= r0)) (PreH29 : (r0 <= UINT_MAX)) (PreH30 : (0 <= remv)) (PreH31 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH32 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH33 : (shift_orig > 0)) (PreH34 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((( &( "r1" ) )) # UInt  |-> r1)
  **  ((( &( "r0" ) )) # UInt  |-> r0)
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ ((Znth i l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_cur 0)) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "r1" ) )) # UInt  |->_)
  **  ((( &( "r0" ) )) # UInt  |->_)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_14 := mpn_div_qr_2_preinv_partial_solve_wit_14_pure -> mpn_div_qr_2_preinv_partial_solve_wit_14_aux.

Definition mpn_div_qr_2_preinv_partial_solve_wit_15 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (qp0_bare <> 0)) (PreH45 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i qp0_bare i 0 (i + 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_16 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (rv0: Z) (rv1: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv1)) (PreH4 : (rv1 <= UINT_MAX)) (PreH5 : (0 <= rv0)) (PreH6 : (rv0 <= UINT_MAX)) (PreH7 : (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH8 : ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 ))) (PreH9 : (i >= 0)) (PreH10 : (0 < d_orig_bare)) (PreH11 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH20 : (0 <= shift_orig)) (PreH21 : (shift_orig < 32)) (PreH22 : (nn0_bare >= 2)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((-1) <= i)) (PreH25 : (i <= (nn0_bare - 2 ))) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r1)) (PreH35 : (r1 <= UINT_MAX)) (PreH36 : (0 <= r0)) (PreH37 : (r0 <= UINT_MAX)) (PreH38 : (0 <= remv)) (PreH39 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH40 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH41 : (shift_orig > 0)) (PreH42 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH43 : (qp0_bare <> 0)) (PreH44 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ ((((r1 * (Z.pow (UINT_MOD) (2)) ) + (r0 * UINT_MOD ) ) + (Znth i l_cur 0) ) = (((qv * ((d1_orig * UINT_MOD ) + d0_orig ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((qp0_bare + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i qp0_bare i 0 (i + 1 ) )
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_17 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig > 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + (1 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 1 0 nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_18 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig > 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + (1 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 1 0 nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_19 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + (1 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 1 0 nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_20 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (i + 1 ) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + (1 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 1 0 nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_21 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig > 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 0 0 nn0_bare (replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_22 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig > 0)) (PreH35 : (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH36 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig > 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_cur)) + (carry * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 0 0 nn0_bare (replace_Znth (1) ((Z.shiftr r1 shift_orig)) (l_cur)) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_23 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) (r1) (l_cur)) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np0_bare + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 0 0 nn0_bare (replace_Znth (1) (r1) (l_cur)) )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_partial_solve_wit_24 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (carry: Z) (remv: Z) (r0: Z) (r1: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (i: Z) (di_orig: Z) (d0_orig: Z) (d1_orig: Z) (shift_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (i < 0)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH6 : (d1_orig <= UINT_MAX)) (PreH7 : (0 <= d0_orig)) (PreH8 : (d0_orig <= UINT_MAX)) (PreH9 : (0 <= di_orig)) (PreH10 : (di_orig <= UINT_MAX)) (PreH11 : (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH12 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) ))) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (nn0_bare >= 2)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((-1) <= i)) (PreH18 : (i <= (nn0_bare - 2 ))) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = ((nn0_bare - 2 ) - i ))) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH24 : (((r1 * UINT_MOD ) + r0 ) = remv)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r1)) (PreH28 : (r1 <= UINT_MAX)) (PreH29 : (0 <= r0)) (PreH30 : (r0 <= UINT_MAX)) (PreH31 : (0 <= remv)) (PreH32 : (remv < ((d1_orig * UINT_MOD ) + d0_orig ))) (PreH33 : (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv ))) (PreH34 : (shift_orig = 0)) (PreH35 : (carry = 0)) (PreH36 : (l_cur = l_np_bare)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare (replace_Znth (1) (r1) (l_cur)) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 0) ” 
  &&  “ (i < 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (((d1_orig * UINT_MOD ) + d0_orig ) = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * ((UINT_MOD * d1_orig ) + d0_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_orig ) + d0_orig ) )) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (nn0_bare >= 2) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (nn0_bare - 2 )) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = ((nn0_bare - 2 ) - i )) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (((r1 * UINT_MOD ) + r0 ) = remv) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (0 <= remv) ” 
  &&  “ (remv < ((d1_orig * UINT_MOD ) + d0_orig )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((nn0_bare - (i + 1 ) ))) ) + (list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (nn0_bare) (l_cur)))) ) = ((qv_done * ((d1_orig * UINT_MOD ) + d0_orig ) ) + remv )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np0_bare + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i np0_bare 0 0 nn0_bare (replace_Znth (1) (r1) (l_cur)) )
  **  (UIntArray.seg qp0_bare (i + 1 ) (nn0_bare - 1 ) l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_2_preinv_derive_optional_by_bare := 
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_optional: Z) (l_np_optional: (@list Z)) (inv0_optional: Z) (nn0_optional: Z) (np0_optional: Z) (qp0_optional: Z) ,
  “ (qp0_optional = qp_pre) ” 
  &&  “ (np0_optional = np_pre) ” 
  &&  “ (nn0_optional = nn_pre) ” 
  &&  “ (inv0_optional = inv_pre) ” 
  &&  “ (nn_pre >= 2) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_optional)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np_optional ) ”
  &&  (optional_q_undef qp_pre (nn_pre - 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np_optional )
  **  (store_div_inverse inv_pre 2 d_orig_optional )
|--
EX (qp0_bare: Z) (np0_bare: Z) (nn0_bare: Z) (inv0_bare: Z) (l_np_bare: (@list Z)) (d_orig_bare: Z) ,
  ((“ (qp0_bare = qp_pre) ” 
  &&  “ (np0_bare = np_pre) ” 
  &&  “ (nn0_bare = nn_pre) ” 
  &&  “ (inv0_bare = inv_pre) ” 
  &&  “ (nn_pre >= 2) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp_pre <> 0) ”
  &&  (UIntArray.undef_full qp_pre (nn_pre - 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 2 d_orig_bare ))
  ||
  (“ (qp0_bare = qp_pre) ” 
  &&  “ (np0_bare = np_pre) ” 
  &&  “ (nn0_bare = nn_pre) ” 
  &&  “ (inv0_bare = inv_pre) ” 
  &&  “ (nn_pre >= 2) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp_pre = 0) ”
  &&  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 2 d_orig_bare )))
  **
  (((EX rv_2 qv_2 l_tail_2 l_rem_2 l_q_2,
  “ ((Zlength (l_q_2)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = 2) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + rv_2 )) ” 
  &&  “ (0 <= rv_2) ” 
  &&  “ (rv_2 < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.seg np0_bare 0 2 l_rem_2 )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail_2 )
  **  (store_div_inverse inv0_bare 2 d_orig_bare ))
  ||
  (EX rv_2 qv_2 l_tail_2 l_rem_2 l_q_2,
  “ ((Zlength (l_q_2)) = (nn0_bare - 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = 2) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0_bare - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + rv_2 )) ” 
  &&  “ (0 <= rv_2) ” 
  &&  “ (rv_2 < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare (nn0_bare - 1 ) l_q_2 )
  **  (UIntArray.seg np0_bare 0 2 l_rem_2 )
  **  (UIntArray.seg np0_bare 2 nn0_bare l_tail_2 )
  **  (store_div_inverse inv0_bare 2 d_orig_bare )))
  -*
  (EX rv qv l_tail l_rem l_q,
  “ ((Zlength (l_q)) = (nn0_optional - 1 )) ” 
  &&  “ ((Zlength (l_rem)) = 2) ” 
  &&  “ ((Zlength (l_tail)) = (nn0_optional - 2 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_optional)) = ((qv * d_orig_optional ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig_optional) ”
  &&  (optional_q_full qp0_optional (nn0_optional - 1 ) l_q )
  **  (UIntArray.seg np0_optional 0 2 l_rem )
  **  (UIntArray.seg np0_optional 2 nn0_optional l_tail )
  **  (store_div_inverse inv0_optional 2 d_orig_optional )))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_1 : mpn_div_qr_2_preinv_safety_wit_1.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_2 : mpn_div_qr_2_preinv_safety_wit_2.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_3 : mpn_div_qr_2_preinv_safety_wit_3.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_4 : mpn_div_qr_2_preinv_safety_wit_4.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_5 : mpn_div_qr_2_preinv_safety_wit_5.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_6 : mpn_div_qr_2_preinv_safety_wit_6.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_7 : mpn_div_qr_2_preinv_safety_wit_7.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_8 : mpn_div_qr_2_preinv_safety_wit_8.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_9 : mpn_div_qr_2_preinv_safety_wit_9.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_10 : mpn_div_qr_2_preinv_safety_wit_10.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_11 : mpn_div_qr_2_preinv_safety_wit_11.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_12 : mpn_div_qr_2_preinv_safety_wit_12.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_13 : mpn_div_qr_2_preinv_safety_wit_13.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_14 : mpn_div_qr_2_preinv_safety_wit_14.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_15 : mpn_div_qr_2_preinv_safety_wit_15.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_16 : mpn_div_qr_2_preinv_safety_wit_16.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_17 : mpn_div_qr_2_preinv_safety_wit_17.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_18 : mpn_div_qr_2_preinv_safety_wit_18.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_19 : mpn_div_qr_2_preinv_safety_wit_19.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_20 : mpn_div_qr_2_preinv_safety_wit_20.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_21 : mpn_div_qr_2_preinv_safety_wit_21.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_22 : mpn_div_qr_2_preinv_safety_wit_22.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_23 : mpn_div_qr_2_preinv_safety_wit_23.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_24 : mpn_div_qr_2_preinv_safety_wit_24.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_25 : mpn_div_qr_2_preinv_safety_wit_25.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_26 : mpn_div_qr_2_preinv_safety_wit_26.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_27 : mpn_div_qr_2_preinv_safety_wit_27.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_28 : mpn_div_qr_2_preinv_safety_wit_28.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_29 : mpn_div_qr_2_preinv_safety_wit_29.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_30 : mpn_div_qr_2_preinv_safety_wit_30.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_31 : mpn_div_qr_2_preinv_safety_wit_31.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_32 : mpn_div_qr_2_preinv_safety_wit_32.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_33 : mpn_div_qr_2_preinv_safety_wit_33.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_34 : mpn_div_qr_2_preinv_safety_wit_34.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_35 : mpn_div_qr_2_preinv_safety_wit_35.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_36 : mpn_div_qr_2_preinv_safety_wit_36.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_37 : mpn_div_qr_2_preinv_safety_wit_37.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_38 : mpn_div_qr_2_preinv_safety_wit_38.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_39 : mpn_div_qr_2_preinv_safety_wit_39.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_40 : mpn_div_qr_2_preinv_safety_wit_40.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_41 : mpn_div_qr_2_preinv_safety_wit_41.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_42 : mpn_div_qr_2_preinv_safety_wit_42.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_43 : mpn_div_qr_2_preinv_safety_wit_43.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_44 : mpn_div_qr_2_preinv_safety_wit_44.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_45 : mpn_div_qr_2_preinv_safety_wit_45.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_46 : mpn_div_qr_2_preinv_safety_wit_46.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_47 : mpn_div_qr_2_preinv_safety_wit_47.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_48 : mpn_div_qr_2_preinv_safety_wit_48.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_49 : mpn_div_qr_2_preinv_safety_wit_49.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_50 : mpn_div_qr_2_preinv_safety_wit_50.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_51 : mpn_div_qr_2_preinv_safety_wit_51.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_52 : mpn_div_qr_2_preinv_safety_wit_52.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_53 : mpn_div_qr_2_preinv_safety_wit_53.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_54 : mpn_div_qr_2_preinv_safety_wit_54.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_55 : mpn_div_qr_2_preinv_safety_wit_55.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_56 : mpn_div_qr_2_preinv_safety_wit_56.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_57 : mpn_div_qr_2_preinv_safety_wit_57.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_58 : mpn_div_qr_2_preinv_safety_wit_58.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_59 : mpn_div_qr_2_preinv_safety_wit_59.
Axiom proof_of_mpn_div_qr_2_preinv_safety_wit_60 : mpn_div_qr_2_preinv_safety_wit_60.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_1_1 : mpn_div_qr_2_preinv_entail_wit_1_1.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_1_2 : mpn_div_qr_2_preinv_entail_wit_1_2.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_2_1 : mpn_div_qr_2_preinv_entail_wit_2_1.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_2_2 : mpn_div_qr_2_preinv_entail_wit_2_2.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_2_3 : mpn_div_qr_2_preinv_entail_wit_2_3.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_2_4 : mpn_div_qr_2_preinv_entail_wit_2_4.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_3_1 : mpn_div_qr_2_preinv_entail_wit_3_1.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_3_2 : mpn_div_qr_2_preinv_entail_wit_3_2.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_3_3 : mpn_div_qr_2_preinv_entail_wit_3_3.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_3_4 : mpn_div_qr_2_preinv_entail_wit_3_4.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_4_1 : mpn_div_qr_2_preinv_entail_wit_4_1.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_4_2 : mpn_div_qr_2_preinv_entail_wit_4_2.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_4_3 : mpn_div_qr_2_preinv_entail_wit_4_3.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_4_4 : mpn_div_qr_2_preinv_entail_wit_4_4.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_5_1 : mpn_div_qr_2_preinv_entail_wit_5_1.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_5_2 : mpn_div_qr_2_preinv_entail_wit_5_2.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_5_3 : mpn_div_qr_2_preinv_entail_wit_5_3.
Axiom proof_of_mpn_div_qr_2_preinv_entail_wit_5_4 : mpn_div_qr_2_preinv_entail_wit_5_4.
Axiom proof_of_mpn_div_qr_2_preinv_return_wit_1 : mpn_div_qr_2_preinv_return_wit_1.
Axiom proof_of_mpn_div_qr_2_preinv_return_wit_2 : mpn_div_qr_2_preinv_return_wit_2.
Axiom proof_of_mpn_div_qr_2_preinv_return_wit_3 : mpn_div_qr_2_preinv_return_wit_3.
Axiom proof_of_mpn_div_qr_2_preinv_return_wit_4 : mpn_div_qr_2_preinv_return_wit_4.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_1_pure : mpn_div_qr_2_preinv_partial_solve_wit_1_pure.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_1 : mpn_div_qr_2_preinv_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_2_pure : mpn_div_qr_2_preinv_partial_solve_wit_2_pure.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_2 : mpn_div_qr_2_preinv_partial_solve_wit_2.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_3 : mpn_div_qr_2_preinv_partial_solve_wit_3.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_4 : mpn_div_qr_2_preinv_partial_solve_wit_4.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_5 : mpn_div_qr_2_preinv_partial_solve_wit_5.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_6 : mpn_div_qr_2_preinv_partial_solve_wit_6.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_7 : mpn_div_qr_2_preinv_partial_solve_wit_7.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_8 : mpn_div_qr_2_preinv_partial_solve_wit_8.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_9 : mpn_div_qr_2_preinv_partial_solve_wit_9.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_10 : mpn_div_qr_2_preinv_partial_solve_wit_10.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_11_pure : mpn_div_qr_2_preinv_partial_solve_wit_11_pure.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_11 : mpn_div_qr_2_preinv_partial_solve_wit_11.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_12_pure : mpn_div_qr_2_preinv_partial_solve_wit_12_pure.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_12 : mpn_div_qr_2_preinv_partial_solve_wit_12.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_13_pure : mpn_div_qr_2_preinv_partial_solve_wit_13_pure.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_13 : mpn_div_qr_2_preinv_partial_solve_wit_13.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_14_pure : mpn_div_qr_2_preinv_partial_solve_wit_14_pure.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_14 : mpn_div_qr_2_preinv_partial_solve_wit_14.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_15 : mpn_div_qr_2_preinv_partial_solve_wit_15.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_16 : mpn_div_qr_2_preinv_partial_solve_wit_16.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_17 : mpn_div_qr_2_preinv_partial_solve_wit_17.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_18 : mpn_div_qr_2_preinv_partial_solve_wit_18.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_19 : mpn_div_qr_2_preinv_partial_solve_wit_19.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_20 : mpn_div_qr_2_preinv_partial_solve_wit_20.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_21 : mpn_div_qr_2_preinv_partial_solve_wit_21.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_22 : mpn_div_qr_2_preinv_partial_solve_wit_22.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_23 : mpn_div_qr_2_preinv_partial_solve_wit_23.
Axiom proof_of_mpn_div_qr_2_preinv_partial_solve_wit_24 : mpn_div_qr_2_preinv_partial_solve_wit_24.
Axiom proof_of_mpn_div_qr_2_preinv_derive_optional_by_bare : mpn_div_qr_2_preinv_derive_optional_by_bare.

End VC_Correct.
