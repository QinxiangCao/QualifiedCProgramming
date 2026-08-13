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

(*----- Function mpn_div_qr_1_preinv -----*)

Definition mpn_div_qr_1_preinv_safety_wit_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "tn" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) (PreH19 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "tn" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) (PreH19 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_5 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) (PreH19 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_6 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (0 < d_orig_bare)) (PreH4 : (0 <= shift_orig)) (PreH5 : (shift_orig < 32)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_7 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare <> 0)) (PreH20 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_8 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig > 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_9 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (shift_orig > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare <> 0)) (PreH21 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_10 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (shift_orig > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_11 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare <> 0)) (PreH20 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_12 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_13 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tp: Z) (tn: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) (PreH22 : (tp <> np0_bare)) (PreH23 : (tn = nn0_bare)) ,
  (UIntArray.full tp nn0_bare l_out )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> tp)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> retval)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_14 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tp: Z) (tn: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) (PreH22 : (tp <> np0_bare)) (PreH23 : (tn = nn0_bare)) ,
  (UIntArray.full tp nn0_bare l_out )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> tp)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_15 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tn: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) (PreH22 : (qp0_bare <> np0_bare)) (PreH23 : (tn = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_out )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> retval)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_16 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tn: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig)) (PreH14 : (d0_orig <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) (PreH22 : (qp0_bare <> np0_bare)) (PreH23 : (tn = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_out )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_17 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare <> 0)) (PreH20 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> 0)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_18 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare <> 0)) (PreH20 : (qp0_bare <> np0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> 0)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_19 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> 0)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ ((nn0_bare - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn0_bare - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_20 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (shift_orig <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig)) (PreH6 : (shift_orig < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig)) (PreH12 : (d0_orig <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "r" ) )) # UInt  |-> 0)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_21 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : ((-1) <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r)) (PreH28 : (r < d1_orig)) (PreH29 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH30 : (shift_orig > 0)) (PreH31 : (qp0_bare = 0)) (PreH32 : (np = tp)) (PreH33 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_22 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : ((-1) <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r)) (PreH28 : (r < d1_orig)) (PreH29 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH30 : (shift_orig > 0)) (PreH31 : (qp0_bare <> 0)) (PreH32 : (np = qp0_bare)) (PreH33 : (tp = qp0_bare)) (PreH34 : (tn = 0)) (PreH35 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_23 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : ((-1) <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r)) (PreH28 : (r < d1_orig)) (PreH29 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH30 : (shift_orig = 0)) (PreH31 : (carry = 0)) (PreH32 : (l_cur = l_np_bare)) (PreH33 : (np = np0_bare)) (PreH34 : (tp = 0)) (PreH35 : (tn = 0)) (PreH36 : (qp0_bare <> 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_24 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : ((-1) <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r)) (PreH28 : (r < d1_orig)) (PreH29 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH30 : (shift_orig = 0)) (PreH31 : (carry = 0)) (PreH32 : (l_cur = l_np_bare)) (PreH33 : (np = np0_bare)) (PreH34 : (tp = 0)) (PreH35 : (tn = 0)) (PreH36 : (qp0_bare = 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_25 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv)) (PreH4 : (rv < d1_orig)) (PreH5 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH6 : (nn >= 0)) (PreH7 : (0 < d_orig_bare)) (PreH8 : (0 <= shift_orig)) (PreH9 : (shift_orig < 32)) (PreH10 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH20 : ((-1) <= nn)) (PreH21 : (nn < nn0_bare)) (PreH22 : (nn0_bare > 0)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH25 : ((Zlength (l_cur)) = nn0_bare)) (PreH26 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH27 : (list_within_bound UINT_MOD l_np_bare )) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (0 <= carry)) (PreH32 : (carry <= UINT_MAX)) (PreH33 : (0 <= r)) (PreH34 : (r < d1_orig)) (PreH35 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH36 : (shift_orig > 0)) (PreH37 : (qp0_bare = 0)) (PreH38 : (np = tp)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_26 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv)) (PreH4 : (rv < d1_orig)) (PreH5 : (((r * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv ))) (PreH6 : (nn >= 0)) (PreH7 : (0 < d_orig_bare)) (PreH8 : (0 <= shift_orig)) (PreH9 : (shift_orig < 32)) (PreH10 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH20 : ((-1) <= nn)) (PreH21 : (nn < nn0_bare)) (PreH22 : (nn0_bare > 0)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH25 : ((Zlength (l_cur)) = nn0_bare)) (PreH26 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH27 : (list_within_bound UINT_MOD l_np_bare )) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (0 <= carry)) (PreH32 : (carry <= UINT_MAX)) (PreH33 : (0 <= r)) (PreH34 : (r < d1_orig)) (PreH35 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH36 : (shift_orig > 0)) (PreH37 : (qp0_bare <> 0)) (PreH38 : (np = qp0_bare)) (PreH39 : (tp = qp0_bare)) (PreH40 : (tn = 0)) (PreH41 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_27 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv)) (PreH4 : (rv < d1_orig)) (PreH5 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH6 : (nn >= 0)) (PreH7 : (0 < d_orig_bare)) (PreH8 : (0 <= shift_orig)) (PreH9 : (shift_orig < 32)) (PreH10 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH20 : ((-1) <= nn)) (PreH21 : (nn < nn0_bare)) (PreH22 : (nn0_bare > 0)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH25 : ((Zlength (l_cur)) = nn0_bare)) (PreH26 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH27 : (list_within_bound UINT_MOD l_np_bare )) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (0 <= carry)) (PreH32 : (carry <= UINT_MAX)) (PreH33 : (0 <= r)) (PreH34 : (r < d1_orig)) (PreH35 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH36 : (shift_orig = 0)) (PreH37 : (carry = 0)) (PreH38 : (l_cur = l_np_bare)) (PreH39 : (np = np0_bare)) (PreH40 : (tp = 0)) (PreH41 : (tn = 0)) (PreH42 : (qp0_bare <> 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_28 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (0 <= qv)) (PreH2 : (qv <= UINT_MAX)) (PreH3 : (0 <= rv)) (PreH4 : (rv < d1_orig)) (PreH5 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH6 : (nn >= 0)) (PreH7 : (0 < d_orig_bare)) (PreH8 : (0 <= shift_orig)) (PreH9 : (shift_orig < 32)) (PreH10 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH11 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH13 : (d1_orig <= UINT_MAX)) (PreH14 : (0 <= d0_orig)) (PreH15 : (d0_orig <= UINT_MAX)) (PreH16 : (0 <= di_orig)) (PreH17 : (di_orig <= UINT_MAX)) (PreH18 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH19 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH20 : ((-1) <= nn)) (PreH21 : (nn < nn0_bare)) (PreH22 : (nn0_bare > 0)) (PreH23 : (nn0_bare <= INT_MAX)) (PreH24 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH25 : ((Zlength (l_cur)) = nn0_bare)) (PreH26 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH27 : (list_within_bound UINT_MOD l_np_bare )) (PreH28 : (list_within_bound UINT_MOD l_cur )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH31 : (0 <= carry)) (PreH32 : (carry <= UINT_MAX)) (PreH33 : (0 <= r)) (PreH34 : (r < d1_orig)) (PreH35 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH36 : (shift_orig = 0)) (PreH37 : (carry = 0)) (PreH38 : (l_cur = l_np_bare)) (PreH39 : (np = np0_bare)) (PreH40 : (tp = 0)) (PreH41 : (tn = 0)) (PreH42 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_29 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig > 0)) (PreH38 : (qp0_bare = 0)) (PreH39 : (np = tp)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_30 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig > 0)) (PreH38 : (qp0_bare <> 0)) (PreH39 : (np = qp0_bare)) (PreH40 : (tp = qp0_bare)) (PreH41 : (tn = 0)) (PreH42 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_31 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig = 0)) (PreH38 : (carry = 0)) (PreH39 : (l_cur = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn = 0)) (PreH43 : (qp0_bare <> 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_32 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig = 0)) (PreH38 : (carry = 0)) (PreH39 : (l_cur = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn = 0)) (PreH43 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_33 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_done: (@list Z)) (qv_done: Z) (carry: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH35 : (shift_orig > 0)) (PreH36 : (np = qp0_bare)) (PreH37 : (tp = qp0_bare)) (PreH38 : (tn = 0)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH40 : (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.full qp0_bare (nn + 1 ) (replace_Znth (nn) (qv) ((sublist (0) ((nn + 1 )) (l_cur)))) )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((nn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_34 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_done: (@list Z)) (qv_done: Z) (carry: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH35 : (shift_orig > 0)) (PreH36 : (np = qp0_bare)) (PreH37 : (tp = qp0_bare)) (PreH38 : (tn = 0)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH40 : (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.full qp0_bare (nn + 1 ) (replace_Znth (nn) (qv) ((sublist (0) ((nn + 1 )) (l_cur)))) )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_35 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_done: (@list Z)) (qv_done: Z) (carry: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH35 : (shift_orig = 0)) (PreH36 : (carry = 0)) (PreH37 : (l_cur = l_np_bare)) (PreH38 : (np = np0_bare)) (PreH39 : (tp = 0)) (PreH40 : (tn = 0)) (PreH41 : (((r_old * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.undef_seg qp0_bare 0 nn )
  **  (((qp0_bare + (nn * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((nn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_36 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_done: (@list Z)) (qv_done: Z) (carry: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH35 : (shift_orig = 0)) (PreH36 : (carry = 0)) (PreH37 : (l_cur = l_np_bare)) (PreH38 : (np = np0_bare)) (PreH39 : (tp = 0)) (PreH40 : (tn = 0)) (PreH41 : (((r_old * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.undef_seg qp0_bare 0 nn )
  **  (((qp0_bare + (nn * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_37 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig > 0)) (PreH38 : (qp0_bare = 0)) (PreH39 : (np = tp)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((nn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_38 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig > 0)) (PreH38 : (qp0_bare = 0)) (PreH39 : (np = tp)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_39 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig = 0)) (PreH38 : (carry = 0)) (PreH39 : (l_cur = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn = 0)) (PreH43 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((nn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nn - 1 )) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_40 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig)) (PreH10 : (shift_orig < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig)) (PreH16 : (d0_orig <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur)) = nn0_bare)) (PreH27 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH32 : (0 <= carry)) (PreH33 : (carry <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH37 : (shift_orig = 0)) (PreH38 : (carry = 0)) (PreH39 : (l_cur = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn = 0)) (PreH43 : (qp0_bare = 0)) ,
  ((( &( "q" ) )) # UInt  |-> qv)
  **  ((( &( "r" ) )) # UInt  |-> rv)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_41 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (tmp_val: Z) (tmp_len: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare = 0)) (PreH29 : (np = tp)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (0 <= tmp_len)) (PreH32 : (tmp_len <= nn0_bare)) (PreH33 : (nn0_bare = 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_42 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare <> 0)) (PreH29 : (tn = 0)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (tn <> 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_43 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (tn <> 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_44 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare = 0)) (PreH34 : (tn <> 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ False ”
.

Definition mpn_div_qr_1_preinv_safety_wit_45 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (tmp_len: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare = 0)) (PreH29 : (np = tp)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (0 <= tmp_len)) (PreH32 : (tmp_len <= nn0_bare)) (PreH33 : (nn0_bare <> 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_46 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare <> 0)) (PreH29 : (tn = 0)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (tn = 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_47 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (tn = 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_1_preinv_safety_wit_48 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare = 0)) (PreH34 : (tn = 0)) ,
  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (shift_orig <= 31) ” 
  &&  “ (0 <= shift_orig) ”
.

Definition mpn_div_qr_1_preinv_entail_wit_1_1 := 
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre > 0)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre <> 0)) (PreH10 : (qp_pre <> np_pre)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.undef_full qp_pre nn_pre )
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 1 d_orig_bare )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> np0_bare) ”
  &&  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre > 0)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre <> 0)) (PreH10 : (qp_pre <> np_pre)) ,
  (UIntArray.undef_full qp_pre nn_pre )
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 1 d_orig_bare )
|--
  EX (x: Z)  (di_orig: Z)  (d0_orig: Z)  (shift_orig: Z) ,
  “ (inv_pre = inv0_bare) ” 
  &&  “ (nn_pre = nn0_bare) ” 
  &&  “ (np_pre = np0_bare) ” 
  &&  “ (qp_pre = qp0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig)) ) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig)) ) ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> np0_bare) ”
  &&  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> x)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (d_orig_bare * (Z.pow (2) (shift_orig)) ))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
).

Definition mpn_div_qr_1_preinv_entail_wit_1_2 := 
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre > 0)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 1 d_orig_bare )
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (PreH1 : (qp0_bare = qp_pre)) (PreH2 : (np0_bare = np_pre)) (PreH3 : (nn0_bare = nn_pre)) (PreH4 : (inv0_bare = inv_pre)) (PreH5 : (nn_pre > 0)) (PreH6 : (nn_pre <= INT_MAX)) (PreH7 : ((Zlength (l_np_bare)) = nn_pre)) (PreH8 : (list_within_bound UINT_MOD l_np_bare )) (PreH9 : (qp_pre = 0)) ,
  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 1 d_orig_bare )
|--
  EX (x: Z)  (di_orig: Z)  (d0_orig: Z)  (shift_orig: Z) ,
  “ (inv_pre = inv0_bare) ” 
  &&  “ (nn_pre = nn0_bare) ” 
  &&  “ (np_pre = np0_bare) ” 
  &&  “ (qp_pre = qp0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig)) ) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig)) ) ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> x)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (d_orig_bare * (Z.pow (2) (shift_orig)) ))
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
).

Definition mpn_div_qr_1_preinv_entail_wit_2_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig_2: Z) (d0_orig_2: Z) (di_orig_2: Z) (retval: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (shift_orig_2 > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (d1_orig_2 = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig_2)) (PreH11 : (d1_orig_2 <= UINT_MAX)) (PreH12 : (0 <= d0_orig_2)) (PreH13 : (d0_orig_2 <= UINT_MAX)) (PreH14 : (0 <= di_orig_2)) (PreH15 : (di_orig_2 <= UINT_MAX)) (PreH16 : (((di_orig_2 + UINT_MOD ) * (UINT_MOD * d1_orig_2 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig_2 ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare = 0)) ,
  (UIntArray.undef_full retval nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig_2)
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
|--
  EX (tp: Z)  (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (tp <> np0_bare) ” 
  &&  “ (nn0_bare = nn0_bare) ”
  &&  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (UIntArray.undef_full tp nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig_2: Z) (d0_orig_2: Z) (di_orig_2: Z) (retval: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (shift_orig_2 > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (d1_orig_2 = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig_2)) (PreH11 : (d1_orig_2 <= UINT_MAX)) (PreH12 : (0 <= d0_orig_2)) (PreH13 : (d0_orig_2 <= UINT_MAX)) (PreH14 : (0 <= di_orig_2)) (PreH15 : (di_orig_2 <= UINT_MAX)) (PreH16 : (((di_orig_2 + UINT_MOD ) * (UINT_MOD * d1_orig_2 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig_2 ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare = 0)) ,
  TT && emp 
|--
  EX (d0_orig: Z) ,
  “ (1 <= shift_orig_2) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (((di_orig_2 + UINT_MOD ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (retval <> np0_bare) ”
  &&  emp
).

Definition mpn_div_qr_1_preinv_entail_wit_2_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig_2: Z) (d0_orig_2: Z) (di_orig_2: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (shift_orig_2 > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (d1_orig_2 = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig_2)) (PreH11 : (d1_orig_2 <= UINT_MAX)) (PreH12 : (0 <= d0_orig_2)) (PreH13 : (d0_orig_2 <= UINT_MAX)) (PreH14 : (0 <= di_orig_2)) (PreH15 : (di_orig_2 <= UINT_MAX)) (PreH16 : (((di_orig_2 + UINT_MOD ) * (UINT_MOD * d1_orig_2 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig_2 ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare <> 0)) (PreH21 : (qp0_bare <> np0_bare)) ,
  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig_2)
|--
  EX (di_orig: Z)  (d0_orig: Z)  (d1_orig: Z)  (shift_orig: Z) ,
  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> np0_bare) ” 
  &&  “ (0 = 0) ”
  &&  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig_2: Z) (d0_orig_2: Z) (di_orig_2: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (shift_orig_2 > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (d1_orig_2 = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig_2)) (PreH11 : (d1_orig_2 <= UINT_MAX)) (PreH12 : (0 <= d0_orig_2)) (PreH13 : (d0_orig_2 <= UINT_MAX)) (PreH14 : (0 <= di_orig_2)) (PreH15 : (di_orig_2 <= UINT_MAX)) (PreH16 : (((di_orig_2 + UINT_MOD ) * (UINT_MOD * d1_orig_2 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig_2 ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare <> 0)) (PreH21 : (qp0_bare <> np0_bare)) ,
  TT && emp 
|--
  EX (d0_orig: Z) ,
  “ (1 <= shift_orig_2) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (((di_orig_2 + UINT_MOD ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig_2 + UINT_MOD ) + 1 ) * (UINT_MOD * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  emp
).

Definition mpn_div_qr_1_preinv_entail_wit_3_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (tp: Z) (tn_4: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig_2)) (PreH14 : (d0_orig_2 <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) (PreH22 : (tp <> np0_bare)) (PreH23 : (tn_4 = nn0_bare)) ,
  (UIntArray.full tp nn0_bare l_out )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (retval * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (tp = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full tp nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (tp: Z) (tn_4: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig_2)) (PreH14 : (d0_orig_2 <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare = 0)) (PreH22 : (tp <> np0_bare)) (PreH23 : (tn_4 = nn0_bare)) ,
  TT && emp 
|--
  EX (carry: Z)  (l_done: (@list Z))  (d0_orig: Z) ,
  “ (0 <= shift_orig_2) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ ((-1) <= ((Zlength (l_out)) - 1 )) ” 
  &&  “ (((Zlength (l_out)) - 1 ) < (Zlength (l_out))) ” 
  &&  “ ((Zlength (l_done)) = ((Zlength (l_out)) - (((Zlength (l_out)) - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((Zlength (l_out)))) ) + (list_to_Z (UINT_MOD) (l_out)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((((Zlength (l_out)) - 1 ) + 1 ))) ) * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) + (retval * (Z.pow (UINT_MOD) ((((Zlength (l_out)) - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((((Zlength (l_out)) - 1 ) + 1 )) (l_out)))) )) ” 
  &&  “ (shift_orig_2 > 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((Zlength (l_out)))) ) + (list_to_Z (UINT_MOD) (l_out)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) )) ”
  &&  emp
).

Definition mpn_div_qr_1_preinv_entail_wit_3_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (tn_4: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig_2)) (PreH14 : (d0_orig_2 <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) (PreH22 : (qp0_bare <> np0_bare)) (PreH23 : (tn_4 = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_out )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tn: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (retval * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare = qp0_bare) ” 
  &&  “ (qp0_bare = qp0_bare) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare 0 ((nn0_bare - 1 ) + 1 ) (sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 1 ) + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (tn_4: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = nn0_bare)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (nn0_bare)) ) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) (PreH4 : (nn0_bare > 0)) (PreH5 : (nn0_bare <= INT_MAX)) (PreH6 : (1 <= shift_orig_2)) (PreH7 : (shift_orig_2 < 32)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH10 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH12 : (d1_orig <= UINT_MAX)) (PreH13 : (0 <= d0_orig_2)) (PreH14 : (d0_orig_2 <= UINT_MAX)) (PreH15 : (0 <= di_orig)) (PreH16 : (di_orig <= UINT_MAX)) (PreH17 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH18 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (qp0_bare <> 0)) (PreH22 : (qp0_bare <> np0_bare)) (PreH23 : (tn_4 = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_out )
|--
  EX (carry: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z) ,
  “ (tn_4 = 0) ” 
  &&  “ (tn_4 = 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig_2) ” 
  &&  “ (shift_orig_2 < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (retval * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig_2 > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) )) ”
  &&  (UIntArray.seg qp0_bare 0 ((nn0_bare - 1 ) + 1 ) (sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 1 ) + 1 ) nn0_bare l_done )
).

Definition mpn_div_qr_1_preinv_entail_wit_3_3 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (PreH1 : (shift_orig_2 <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig_2)) (PreH6 : (shift_orig_2 < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig_2)) (PreH12 : (d0_orig_2 <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare <> 0)) (PreH20 : (qp0_bare <> np0_bare)) ,
  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  EX (tn_2: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (0 * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np0_bare = np0_bare) ” 
  &&  “ (0 = 0) ” 
  &&  “ (tn_2 = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> tn_2)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 ((nn0_bare - 1 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 1 ) + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (PreH1 : (shift_orig_2 <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig_2)) (PreH6 : (shift_orig_2 < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig_2)) (PreH12 : (d0_orig_2 <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare <> 0)) (PreH20 : (qp0_bare <> np0_bare)) ,
  (UIntArray.undef_full qp0_bare nn0_bare )
|--
  EX (l_done: (@list Z))  (d0_orig: Z) ,
  “ (shift_orig_2 = 0) ” 
  &&  “ (shift_orig_2 = 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (0)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (0)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < d1_orig) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_np_bare)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (0 * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_np_bare)))) )) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.undef_seg qp0_bare 0 ((nn0_bare - 1 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn0_bare - 1 ) + 1 ) nn0_bare l_done )
).

Definition mpn_div_qr_1_preinv_entail_wit_3_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (PreH1 : (shift_orig_2 <= 0)) (PreH2 : (nn0_bare > 0)) (PreH3 : (nn0_bare <= INT_MAX)) (PreH4 : (0 < d_orig_bare)) (PreH5 : (0 <= shift_orig_2)) (PreH6 : (shift_orig_2 < 32)) (PreH7 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH8 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH10 : (d1_orig <= UINT_MAX)) (PreH11 : (0 <= d0_orig_2)) (PreH12 : (d0_orig_2 <= UINT_MAX)) (PreH13 : (0 <= di_orig)) (PreH14 : (di_orig <= UINT_MAX)) (PreH15 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : (list_within_bound UINT_MOD l_np_bare )) (PreH19 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "tn" ) )) # Int  |-> 0)
|--
  (EX (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (0 * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np0_bare = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tn_3: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn0_bare - 1 )) ” 
  &&  “ ((nn0_bare - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn0_bare - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) * d1_orig ) + (0 * (Z.pow (UINT_MOD) (((nn0_bare - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn0_bare - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np0_bare = np0_bare) ” 
  &&  “ (0 = 0) ” 
  &&  “ (tn_3 = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> tn_3)
  **  (UIntArray.full np0_bare nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_1_preinv_entail_wit_4_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur_2)) 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 > 0)) (PreH38 : (qp0_bare <> 0)) (PreH39 : (np = qp0_bare)) (PreH40 : (tp = qp0_bare)) (PreH41 : (tn = 0)) (PreH42 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur_2)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (r_old: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (0 <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r_old) ” 
  &&  “ (r_old < d1_orig) ” 
  &&  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (np = qp0_bare) ” 
  &&  “ (tp = qp0_bare) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv )) ”
  &&  (UIntArray.seg qp0_bare 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur_2)) 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 > 0)) (PreH38 : (qp0_bare <> 0)) (PreH39 : (np = qp0_bare)) (PreH40 : (tp = qp0_bare)) (PreH41 : (tn = 0)) (PreH42 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  TT && emp 
|--
  EX (r_old: Z)  (carry: Z)  (l_cur: (@list Z))  (d0_orig: Z) ,
  “ ((sublist (0) ((nn + 1 )) (l_cur_2)) = (sublist (0) ((nn + 1 )) (l_cur))) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= nn) ” 
  &&  “ ((Zlength (l_cur)) = (Zlength (l_np_bare))) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r_old) ” 
  &&  “ (r_old < (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((Zlength (l_np_bare)))) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((Zlength (l_np_bare)))) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) + rv )) ”
  &&  emp
).

Definition mpn_div_qr_1_preinv_entail_wit_4_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 = 0)) (PreH38 : (carry_2 = 0)) (PreH39 : (l_cur_2 = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn = 0)) (PreH43 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur_2 )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (r_old: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (0 <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r_old) ” 
  &&  “ (r_old < d1_orig) ” 
  &&  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((r_old * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv )) ”
  &&  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare <> 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 = 0)) (PreH38 : (carry_2 = 0)) (PreH39 : (l_cur_2 = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn = 0)) (PreH43 : (qp0_bare <> 0)) ,
  TT && emp 
|--
  EX (r_old: Z)  (d0_orig: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 < 32) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (0)) ) = (d_orig_bare * (Z.pow (2) (0)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (0)) ) < UINT_MOD) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= nn) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= r_old) ” 
  &&  “ (r_old < (d_orig_bare * (Z.pow (2) (0)) )) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) ((Zlength (l_np_bare)))) ) + (list_to_Z (UINT_MOD) (l_np_bare)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * (d_orig_bare * (Z.pow (2) (0)) ) ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_np_bare)))) )) ” 
  &&  “ (((r_old * UINT_MOD ) + (Znth nn l_np_bare 0) ) = ((qv * (d_orig_bare * (Z.pow (2) (0)) ) ) + rv )) ”
  &&  emp
).

Definition mpn_div_qr_1_preinv_entail_wit_5_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (l_cur_2: (@list Z)) (l_done_2: (@list Z)) (qv_done_2: Z) (carry_2: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn_4: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig_2)) (PreH3 : (shift_orig_2 < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig_2)) (PreH9 : (d0_orig_2 <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH20 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur_2 )) (PreH23 : (list_within_bound UINT_MOD l_done_2 )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH25 : (0 <= carry_2)) (PreH26 : (carry_2 <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH35 : (shift_orig_2 > 0)) (PreH36 : (np = qp0_bare)) (PreH37 : (tp = qp0_bare)) (PreH38 : (tn_4 = 0)) (PreH39 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) (PreH40 : (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur_2)) 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.full qp0_bare (nn + 1 ) (replace_Znth (nn) (qv) ((sublist (0) ((nn + 1 )) (l_cur_2)))) )
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tn: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (np = qp0_bare) ” 
  &&  “ (tp = qp0_bare) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg np 0 ((nn - 1 ) + 1 ) (sublist (0) (((nn - 1 ) + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare ((nn - 1 ) + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (l_cur_2: (@list Z)) (l_done_2: (@list Z)) (qv_done_2: Z) (carry_2: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn_4: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig_2)) (PreH3 : (shift_orig_2 < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig_2)) (PreH9 : (d0_orig_2 <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH20 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur_2 )) (PreH23 : (list_within_bound UINT_MOD l_done_2 )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH25 : (0 <= carry_2)) (PreH26 : (carry_2 <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH35 : (shift_orig_2 > 0)) (PreH36 : (np = qp0_bare)) (PreH37 : (tp = qp0_bare)) (PreH38 : (tn_4 = 0)) (PreH39 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) (PreH40 : (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur_2)) 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.full qp0_bare (nn + 1 ) (replace_Znth (nn) (qv) ((sublist (0) ((nn + 1 )) (l_cur_2)))) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done_2 )
|--
  EX (carry: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z) ,
  “ (tn_4 = 0) ” 
  &&  “ (tn_4 = 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig_2) ” 
  &&  “ (shift_orig_2 < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig_2 > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (np = qp0_bare) ” 
  &&  “ (tp = qp0_bare) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) )) ”
  &&  (UIntArray.seg np 0 ((nn - 1 ) + 1 ) (sublist (0) (((nn - 1 ) + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare ((nn - 1 ) + 1 ) nn0_bare l_done )
).

Definition mpn_div_qr_1_preinv_entail_wit_5_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (l_cur_2: (@list Z)) (l_done_2: (@list Z)) (qv_done_2: Z) (carry_2: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn_4: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig_2)) (PreH3 : (shift_orig_2 < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig_2)) (PreH9 : (d0_orig_2 <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH20 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur_2 )) (PreH23 : (list_within_bound UINT_MOD l_done_2 )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH25 : (0 <= carry_2)) (PreH26 : (carry_2 <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH35 : (shift_orig_2 = 0)) (PreH36 : (carry_2 = 0)) (PreH37 : (l_cur_2 = l_np_bare)) (PreH38 : (np = np0_bare)) (PreH39 : (tp = 0)) (PreH40 : (tn_4 = 0)) (PreH41 : (((r_old * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.undef_seg qp0_bare 0 nn )
  **  (((qp0_bare + (nn * sizeof(UINT)))) # UInt  |-> qv)
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  (UIntArray.full np nn0_bare l_cur_2 )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tn_2: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn_2 = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> tn_2)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 ((nn - 1 ) + 1 ) )
  **  (UIntArray.seg qp0_bare ((nn - 1 ) + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig_2: Z) (d1_orig: Z) (d0_orig_2: Z) (di_orig: Z) (l_cur_2: (@list Z)) (l_done_2: (@list Z)) (qv_done_2: Z) (carry_2: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn_4: Z) (PreH1 : (qv >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig_2)) (PreH4 : (shift_orig_2 < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig_2)) (PreH10 : (d0_orig_2 <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : (0 <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH21 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur_2 )) (PreH24 : (list_within_bound UINT_MOD l_done_2 )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH26 : (0 <= carry_2)) (PreH27 : (carry_2 <= UINT_MAX)) (PreH28 : (0 <= r_old)) (PreH29 : (r_old < d1_orig)) (PreH30 : (0 <= qv)) (PreH31 : (qv <= UINT_MAX)) (PreH32 : (0 <= rv)) (PreH33 : (rv < d1_orig)) (PreH34 : (qp0_bare <> 0)) (PreH35 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH36 : (shift_orig_2 = 0)) (PreH37 : (carry_2 = 0)) (PreH38 : (l_cur_2 = l_np_bare)) (PreH39 : (np = np0_bare)) (PreH40 : (tp = 0)) (PreH41 : (tn_4 = 0)) (PreH42 : (((r_old * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) ,
  (((qp0_bare + (nn * sizeof(UINT)))) # UInt  |-> qv)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done_2 )
|--
  EX (l_done: (@list Z))  (d0_orig: Z) ,
  “ (l_cur_2 = l_np_bare) ” 
  &&  “ (tn_4 = 0) ” 
  &&  “ (shift_orig_2 = 0) ” 
  &&  “ (shift_orig_2 = 0) ” 
  &&  “ (tn_4 = 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (0)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (0)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((0 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_np_bare)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_np_bare)))) )) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.seg qp0_bare ((nn - 1 ) + 1 ) nn0_bare l_done )
).

Definition mpn_div_qr_1_preinv_entail_wit_5_3 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 > 0)) (PreH38 : (qp0_bare = 0)) (PreH39 : (np = tp)) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  (UIntArray.full np nn0_bare l_cur_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 > 0)) (PreH38 : (qp0_bare = 0)) (PreH39 : (np = tp)) (PreH40 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  TT && emp 
|--
  EX (carry: Z)  (l_done: (@list Z))  (d0_orig: Z) ,
  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < (Zlength (l_np_bare))) ” 
  &&  “ ((Zlength (l_done)) = ((Zlength (l_np_bare)) - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((Zlength (l_np_bare)))) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * (d_orig_bare * (Z.pow (2) (shift_orig_2)) ) ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur_2)))) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) ((Zlength (l_np_bare)))) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) )) ”
  &&  emp
).

Definition mpn_div_qr_1_preinv_entail_wit_5_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn_4: Z) (tp: Z) (np: Z) (r: Z) (carry_2: Z) (qv_done_2: Z) (l_done_2: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (rv: Z) (qv: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (0 <= qv)) (PreH3 : (qv <= UINT_MAX)) (PreH4 : (0 <= rv)) (PreH5 : (rv < d1_orig)) (PreH6 : (((r * UINT_MOD ) + (Znth nn l_cur_2 0) ) = ((qv * d1_orig ) + rv ))) (PreH7 : (nn >= 0)) (PreH8 : (0 < d_orig_bare)) (PreH9 : (0 <= shift_orig_2)) (PreH10 : (shift_orig_2 < 32)) (PreH11 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH12 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH13 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH14 : (d1_orig <= UINT_MAX)) (PreH15 : (0 <= d0_orig_2)) (PreH16 : (d0_orig_2 <= UINT_MAX)) (PreH17 : (0 <= di_orig)) (PreH18 : (di_orig <= UINT_MAX)) (PreH19 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH21 : ((-1) <= nn)) (PreH22 : (nn < nn0_bare)) (PreH23 : (nn0_bare > 0)) (PreH24 : (nn0_bare <= INT_MAX)) (PreH25 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH26 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH27 : ((Zlength (l_done_2)) = (nn0_bare - (nn + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_np_bare )) (PreH29 : (list_within_bound UINT_MOD l_cur_2 )) (PreH30 : (list_within_bound UINT_MOD l_done_2 )) (PreH31 : ((list_to_Z (UINT_MOD) (l_done_2)) = qv_done_2)) (PreH32 : (0 <= carry_2)) (PreH33 : (carry_2 <= UINT_MAX)) (PreH34 : (0 <= r)) (PreH35 : (r < d1_orig)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done_2)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH37 : (shift_orig_2 = 0)) (PreH38 : (carry_2 = 0)) (PreH39 : (l_cur_2 = l_np_bare)) (PreH40 : (np = np0_bare)) (PreH41 : (tp = 0)) (PreH42 : (tn_4 = 0)) (PreH43 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur_2 )
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tn_3: Z)  (carry: Z)  (qv_done: Z)  (l_done: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= (nn - 1 )) ” 
  &&  “ ((nn - 1 ) < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - ((nn - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) * d1_orig ) + (rv * (Z.pow (UINT_MOD) (((nn - 1 ) + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) (((nn - 1 ) + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn_3 = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> tn_3)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_1_preinv_entail_wit_6_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp_4: Z) (np_4: Z) (r: Z) (carry_2: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig_2)) (PreH4 : (shift_orig_2 < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig_2)) (PreH10 : (d0_orig_2 <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur_2 )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry_2)) (PreH27 : (carry_2 <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH31 : (shift_orig_2 > 0)) (PreH32 : (qp0_bare = 0)) (PreH33 : (np_4 = tp_4)) (PreH34 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  ((( &( "np" ) )) # Ptr  |-> np_4)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_4)
  **  (UIntArray.full np_4 nn0_bare l_cur_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tmp_val: Z)  (tmp_len: Z)  (tp: Z)  (np: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (nn0_bare: Z) (qp0_bare: Z) (tp_4: Z) (np_4: Z) (r: Z) (carry_2: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig_2)) (PreH4 : (shift_orig_2 < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig_2)) (PreH10 : (d0_orig_2 <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur_2 )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry_2)) (PreH27 : (carry_2 <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH31 : (shift_orig_2 > 0)) (PreH32 : (qp0_bare = 0)) (PreH33 : (np_4 = tp_4)) (PreH34 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  (UIntArray.full np_4 nn0_bare l_cur_2 )
|--
  EX (tmp_val: Z)  (tmp_len: Z)  (carry: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z) ,
  “ (tp_4 = np_4) ” 
  &&  “ (tp_4 = np_4) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig_2) ” 
  &&  “ (shift_orig_2 < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((list_to_Z (UINT_MOD) (l_q)) * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig_2 > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ”
  &&  (mpd_store_Z_compact UINT_MOD np_4 tmp_val tmp_len )
  **  (UIntArray.undef_seg np_4 tmp_len nn0_bare )
).

Definition mpn_div_qr_1_preinv_entail_wit_6_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn_4: Z) (tp_4: Z) (np_4: Z) (r: Z) (carry_2: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig_2)) (PreH4 : (shift_orig_2 < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig_2)) (PreH10 : (d0_orig_2 <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur_2 )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry_2)) (PreH27 : (carry_2 <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH31 : (shift_orig_2 > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (np_4 = qp0_bare)) (PreH34 : (tp_4 = qp0_bare)) (PreH35 : (tn_4 = 0)) (PreH36 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig_2)) ))) ,
  ((( &( "np" ) )) # Ptr  |-> np_4)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_4)
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  (UIntArray.seg np_4 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur_2)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (tn: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tn_2: Z)  (tp_2: Z)  (np_2: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np_2 = np0_bare) ” 
  &&  “ (tp_2 = 0) ” 
  &&  “ (tn_2 = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np_2)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_2)
  **  ((( &( "tn" ) )) # Int  |-> tn_2)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_1_preinv_entail_wit_6_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn_4: Z) (tp_4: Z) (np_4: Z) (r: Z) (carry_2: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig_2)) (PreH4 : (shift_orig_2 < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig_2)) (PreH10 : (d0_orig_2 <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur_2 )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry_2)) (PreH27 : (carry_2 <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH31 : (shift_orig_2 = 0)) (PreH32 : (carry_2 = 0)) (PreH33 : (l_cur_2 = l_np_bare)) (PreH34 : (np_4 = np0_bare)) (PreH35 : (tp_4 = 0)) (PreH36 : (tn_4 = 0)) (PreH37 : (qp0_bare <> 0)) ,
  ((( &( "np" ) )) # Ptr  |-> np_4)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_4)
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  (UIntArray.full np_4 nn0_bare l_cur_2 )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (tn: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tn_2: Z)  (tp_2: Z)  (np_2: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np_2 = np0_bare) ” 
  &&  “ (tp_2 = 0) ” 
  &&  “ (tn_2 = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np_2)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_2)
  **  ((( &( "tn" ) )) # Int  |-> tn_2)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_1_preinv_entail_wit_6_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn_4: Z) (tp_4: Z) (np_4: Z) (r: Z) (carry_2: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur_2: (@list Z)) (nn: Z) (d0_orig_2: Z) (shift_orig_2: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn < 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig_2)) (PreH4 : (shift_orig_2 < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig_2)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig_2)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig_2)) (PreH10 : (d0_orig_2 <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur_2)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur_2 )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry_2)) (PreH27 : (carry_2 <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry_2 * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur_2)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur_2)))) ))) (PreH31 : (shift_orig_2 = 0)) (PreH32 : (carry_2 = 0)) (PreH33 : (l_cur_2 = l_np_bare)) (PreH34 : (np_4 = np0_bare)) (PreH35 : (tp_4 = 0)) (PreH36 : (tn_4 = 0)) (PreH37 : (qp0_bare = 0)) ,
  ((( &( "np" ) )) # Ptr  |-> np_4)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_4)
  **  ((( &( "tn" ) )) # Int  |-> tn_4)
  **  (UIntArray.full np_4 nn0_bare l_cur_2 )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig_2)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (EX (tmp_val: Z)  (tmp_len: Z)  (tp: Z)  (np: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tn_3: Z)  (tp_3: Z)  (np_3: Z)  (carry: Z)  (qv: Z)  (l_q: (@list Z))  (l_cur: (@list Z))  (d0_orig: Z)  (shift_orig: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np_3 = np0_bare) ” 
  &&  “ (tp_3 = 0) ” 
  &&  “ (tn_3 = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np_3)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_3)
  **  ((( &( "tn" ) )) # Int  |-> tn_3)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_1_preinv_entail_wit_7_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (tmp_val: Z) (tmp_len: Z) (nn: Z) (r: Z) (np_3: Z) (tp_3: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare = 0)) (PreH29 : (np_3 = tp_3)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (0 <= tmp_len)) (PreH32 : (tmp_len <= nn0_bare)) (PreH33 : (nn0_bare = 0)) ,
  ((( &( "np" ) )) # Ptr  |-> np_3)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_3)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp_3 tmp_val tmp_len )
  **  (UIntArray.undef_seg tp_3 tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (“ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (nn0_bare = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (nn0_bare = 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tp: Z)  (np: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (nn0_bare = 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (nn0_bare = 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
  ||
  (EX (tp_2: Z)  (np_2: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np_2 = np0_bare) ” 
  &&  “ (tp_2 = 0) ” 
  &&  “ (nn0_bare = 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (nn0_bare = 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np_2)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_2)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig))
.

Definition mpn_div_qr_1_preinv_entail_wit_7_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare <> 0)) (PreH29 : (tn = 0)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (tn = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (tn = 0) ”
  &&  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_entail_wit_7_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (tn = 0)) ,
  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (tn = 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_entail_wit_7_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np_2: Z) (tp_2: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np_2 = np0_bare)) (PreH31 : (tp_2 = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare = 0)) (PreH34 : (tn = 0)) ,
  ((( &( "np" ) )) # Ptr  |-> np_2)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_2)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np_2 = np0_bare) ” 
  &&  “ (tp_2 = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (tn = 0) ”
  &&  ((( &( "np" ) )) # Ptr  |-> np_2)
  **  ((( &( "tp" ) )) # Ptr  |-> tp_2)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_entail_wit_8_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (tmp_val: Z) (tmp_len: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare = 0)) (PreH29 : (np = tp)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (0 <= tmp_len)) (PreH32 : (tmp_len <= nn0_bare)) (PreH33 : (nn0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ” 
  &&  “ (nn0_bare <> 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_entail_wit_8_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare <> 0)) (PreH29 : (tn = 0)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (tn <> 0)) ,
  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tmp_val: Z)  (tmp_len: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (qp0_bare = qp0_bare) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ” 
  &&  “ (nn0_bare <> 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD qp0_bare tmp_val tmp_len )
  **  (UIntArray.undef_seg qp0_bare tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_entail_wit_8_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (tn <> 0)) ,
  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tmp_val: Z)  (tmp_len: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ” 
  &&  “ (nn0_bare <> 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_entail_wit_8_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare = 0)) (PreH34 : (tn <> 0)) ,
  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (tmp_val: Z)  (tmp_len: Z) ,
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ” 
  &&  “ (nn0_bare <> 0) ”
  &&  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_return_wit_1 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q_2)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare = 0)) (PreH34 : (tn = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (qv: Z)  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + (Z.shiftr r shift_orig) )) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (store_div_inverse inv0_bare 1 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare = 0)) (PreH38 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig_bare ) + (Z.shiftr r shift_orig) )) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (store_div_inverse inv0_bare 1 d_orig_bare )
).

Definition mpn_div_qr_1_preinv_return_wit_2 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q_2)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig = 0)) (PreH28 : (carry = 0)) (PreH29 : (l_cur = l_np_bare)) (PreH30 : (np = np0_bare)) (PreH31 : (tp = 0)) (PreH32 : (tn = 0)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (tn = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_q_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (qv: Z)  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + (Z.shiftr r shift_orig) )) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (store_div_inverse inv0_bare 1 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) (PreH38 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Z.shiftr r 0) < d_orig_bare) ” 
  &&  “ (0 <= (Z.shiftr r 0)) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + (Z.shiftr r 0) )) ”
  &&  (store_div_inverse inv0_bare 1 d_orig_bare )
).

Definition mpn_div_qr_1_preinv_return_wit_2_split_goal_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) (PreH38 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Z.shiftr r 0) < d_orig_bare) ”
.

Definition mpn_div_qr_1_preinv_return_wit_2_split_goal_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) (PreH38 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Z.shiftr r 0)) ”
.

Definition mpn_div_qr_1_preinv_return_wit_2_split_goal_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) (PreH38 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + (Z.shiftr r 0) )) ”
.

Definition mpn_div_qr_1_preinv_return_wit_2_split_goal_spatial := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) (PreH38 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (store_div_inverse inv0_bare 1 d_orig_bare )
.

Definition mpn_div_qr_1_preinv_return_wit_3 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q_2)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare <> 0)) (PreH29 : (tn = 0)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (tn = 0)) ,
  (UIntArray.full qp0_bare nn0_bare l_q_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (qv: Z)  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + (Z.shiftr r shift_orig) )) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare nn0_bare l_q )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (store_div_inverse inv0_bare 1 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (tn = 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + (Z.shiftr r shift_orig) )) ”
  &&  (store_div_inverse inv0_bare 1 d_orig_bare )
).

Definition mpn_div_qr_1_preinv_return_wit_3_split_goal_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (tn = 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Z.shiftr r shift_orig) < d_orig_bare) ”
.

Definition mpn_div_qr_1_preinv_return_wit_3_split_goal_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (tn = 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Z.shiftr r shift_orig)) ”
.

Definition mpn_div_qr_1_preinv_return_wit_3_split_goal_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (tn = 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + (Z.shiftr r shift_orig) )) ”
.

Definition mpn_div_qr_1_preinv_return_wit_3_split_goal_spatial := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (nn: Z) (r: Z) (tn: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (tn = 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (tn = 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  (store_div_inverse inv0_bare 1 d_orig_bare )
.

Definition mpn_div_qr_1_preinv_return_wit_4 := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (tmp_len: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q_2)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare = 0)) (PreH29 : (np = tp)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (0 <= tmp_len)) (PreH32 : (tmp_len <= nn0_bare)) (PreH33 : (nn0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (qv: Z)  (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv * d_orig_bare ) + (Z.shiftr r shift_orig) )) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (store_div_inverse inv0_bare 1 d_orig_bare )
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q_2: (@list Z)) (qv_2: Z) (carry: Z) (tmp_len: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (di_orig >= 0)) (PreH3 : (d1_orig >= 0)) (PreH4 : (shift_orig >= 0)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : (nn = (-1))) (PreH19 : (nn0_bare > 0)) (PreH20 : (nn0_bare <= INT_MAX)) (PreH21 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH22 : ((Zlength (l_cur)) = nn0_bare)) (PreH23 : ((Zlength (l_q_2)) = nn0_bare)) (PreH24 : (list_within_bound UINT_MOD l_np_bare )) (PreH25 : (list_within_bound UINT_MOD l_cur )) (PreH26 : (list_within_bound UINT_MOD l_q_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH28 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv_2 * d1_orig ) + r ))) (PreH29 : (0 <= r)) (PreH30 : (r < d1_orig)) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare = 0)) (PreH33 : (np = tp)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH35 : (0 <= tmp_len)) (PreH36 : (tmp_len <= nn0_bare)) (PreH37 : (nn0_bare <> 0)) ,
  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  EX (l_q: (@list Z)) ,
  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig_bare ) + (Z.shiftr r shift_orig) )) ” 
  &&  “ (0 <= (Z.shiftr r shift_orig)) ” 
  &&  “ ((Z.shiftr r shift_orig) < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (store_div_inverse inv0_bare 1 d_orig_bare )
).

Definition mpn_div_qr_1_preinv_partial_solve_wit_1_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (shift_orig > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
|--
  “ (nn0_bare >= 0) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_1_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (PreH1 : (qp0_bare = 0)) (PreH2 : (shift_orig > 0)) (PreH3 : (nn0_bare > 0)) (PreH4 : (nn0_bare <= INT_MAX)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (0 <= shift_orig)) (PreH7 : (shift_orig < 32)) (PreH8 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH9 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH10 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH11 : (d1_orig <= UINT_MAX)) (PreH12 : (0 <= d0_orig)) (PreH13 : (d0_orig <= UINT_MAX)) (PreH14 : (0 <= di_orig)) (PreH15 : (di_orig <= UINT_MAX)) (PreH16 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH17 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : (list_within_bound UINT_MOD l_np_bare )) (PreH20 : (qp0_bare = 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (nn0_bare >= 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_1 := mpn_div_qr_1_preinv_partial_solve_wit_1_pure -> mpn_div_qr_1_preinv_partial_solve_wit_1_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_2_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tp: Z) (tn: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (1 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) (PreH19 : (tp <> np0_bare)) (PreH20 : (tn = nn0_bare)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_full tp nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
|--
  “ (tp <> np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_2_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tp: Z) (tn: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (1 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare = 0)) (PreH19 : (tp <> np0_bare)) (PreH20 : (tn = nn0_bare)) ,
  (UIntArray.undef_full tp nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (tp <> np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (tp <> np0_bare) ” 
  &&  “ (tn = nn0_bare) ”
  &&  (UIntArray.undef_full tp nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_2 := mpn_div_qr_1_preinv_partial_solve_wit_2_pure -> mpn_div_qr_1_preinv_partial_solve_wit_2_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_3_pure := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tn: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (1 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) (PreH19 : (qp0_bare <> np0_bare)) (PreH20 : (tn = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "tp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
  **  ((( &( "d" ) )) # UInt  |->_)
  **  ((( &( "di" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
|--
  “ (qp0_bare <> np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_3_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (tn: Z) (PreH1 : (nn0_bare > 0)) (PreH2 : (nn0_bare <= INT_MAX)) (PreH3 : (1 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (0 < d_orig_bare)) (PreH6 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH7 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH9 : (d1_orig <= UINT_MAX)) (PreH10 : (0 <= d0_orig)) (PreH11 : (d0_orig <= UINT_MAX)) (PreH12 : (0 <= di_orig)) (PreH13 : (di_orig <= UINT_MAX)) (PreH14 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH16 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH17 : (list_within_bound UINT_MOD l_np_bare )) (PreH18 : (qp0_bare <> 0)) (PreH19 : (qp0_bare <> np0_bare)) (PreH20 : (tn = 0)) ,
  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (qp0_bare <> np0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ (1 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (qp0_bare <> np0_bare) ” 
  &&  “ (tn = 0) ”
  &&  (UIntArray.undef_full qp0_bare nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_3 := mpn_div_qr_1_preinv_partial_solve_wit_3_pure -> mpn_div_qr_1_preinv_partial_solve_wit_3_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare = 0)) (PreH33 : (np = tp)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  (((np + (nn * sizeof(UINT)))) # UInt  |-> (Znth nn l_cur 0))
  **  (UIntArray.missing_i np nn 0 nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_5 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (np = qp0_bare)) (PreH34 : (tp = qp0_bare)) (PreH35 : (tn = 0)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (np = qp0_bare) ” 
  &&  “ (tp = qp0_bare) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  (((np + (nn * sizeof(UINT)))) # UInt  |-> (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0))
  **  (UIntArray.missing_i np nn 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_6 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (((np + (nn * sizeof(UINT)))) # UInt  |-> (Znth nn l_cur 0))
  **  (UIntArray.missing_i np nn 0 nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_7 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (((np + (nn * sizeof(UINT)))) # UInt  |-> (Znth nn l_cur 0))
  **  (UIntArray.missing_i np nn 0 nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_8_pure := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare = 0)) (PreH33 : (np = tp)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_cur 0)) ”
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (nn <= INT_MAX)) (PreH8 : (nn0_bare >= INT_MIN)) (PreH9 : (nn >= INT_MIN)) (PreH10 : (nn >= 0)) (PreH11 : (0 < d_orig_bare)) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH15 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH16 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH17 : (d1_orig <= UINT_MAX)) (PreH18 : (0 <= d0_orig)) (PreH19 : (d0_orig <= UINT_MAX)) (PreH20 : (0 <= di_orig)) (PreH21 : (di_orig <= UINT_MAX)) (PreH22 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH23 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH24 : ((-1) <= nn)) (PreH25 : (nn < nn0_bare)) (PreH26 : (nn0_bare > 0)) (PreH27 : (nn0_bare <= INT_MAX)) (PreH28 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH29 : ((Zlength (l_cur)) = nn0_bare)) (PreH30 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH31 : (list_within_bound UINT_MOD l_np_bare )) (PreH32 : (list_within_bound UINT_MOD l_cur )) (PreH33 : (list_within_bound UINT_MOD l_done )) (PreH34 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH35 : (0 <= carry)) (PreH36 : (carry <= UINT_MAX)) (PreH37 : (0 <= r)) (PreH38 : (r < d1_orig)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH40 : (shift_orig > 0)) (PreH41 : (qp0_bare = 0)) (PreH42 : (np = tp)) (PreH43 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_cur 0)) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ”
).

Definition mpn_div_qr_1_preinv_partial_solve_wit_8_pure_split_goal_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (nn <= INT_MAX)) (PreH8 : (nn0_bare >= INT_MIN)) (PreH9 : (nn >= INT_MIN)) (PreH10 : (nn >= 0)) (PreH11 : (0 < d_orig_bare)) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH15 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH16 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH17 : (d1_orig <= UINT_MAX)) (PreH18 : (0 <= d0_orig)) (PreH19 : (d0_orig <= UINT_MAX)) (PreH20 : (0 <= di_orig)) (PreH21 : (di_orig <= UINT_MAX)) (PreH22 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH23 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH24 : ((-1) <= nn)) (PreH25 : (nn < nn0_bare)) (PreH26 : (nn0_bare > 0)) (PreH27 : (nn0_bare <= INT_MAX)) (PreH28 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH29 : ((Zlength (l_cur)) = nn0_bare)) (PreH30 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH31 : (list_within_bound UINT_MOD l_np_bare )) (PreH32 : (list_within_bound UINT_MOD l_cur )) (PreH33 : (list_within_bound UINT_MOD l_done )) (PreH34 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH35 : (0 <= carry)) (PreH36 : (carry <= UINT_MAX)) (PreH37 : (0 <= r)) (PreH38 : (r < d1_orig)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH40 : (shift_orig > 0)) (PreH41 : (qp0_bare = 0)) (PreH42 : (np = tp)) (PreH43 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_cur 0)) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_8_pure_split_goal_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (nn <= INT_MAX)) (PreH8 : (nn0_bare >= INT_MIN)) (PreH9 : (nn >= INT_MIN)) (PreH10 : (nn >= 0)) (PreH11 : (0 < d_orig_bare)) (PreH12 : (0 <= shift_orig)) (PreH13 : (shift_orig < 32)) (PreH14 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH15 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH16 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH17 : (d1_orig <= UINT_MAX)) (PreH18 : (0 <= d0_orig)) (PreH19 : (d0_orig <= UINT_MAX)) (PreH20 : (0 <= di_orig)) (PreH21 : (di_orig <= UINT_MAX)) (PreH22 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH23 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH24 : ((-1) <= nn)) (PreH25 : (nn < nn0_bare)) (PreH26 : (nn0_bare > 0)) (PreH27 : (nn0_bare <= INT_MAX)) (PreH28 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH29 : ((Zlength (l_cur)) = nn0_bare)) (PreH30 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH31 : (list_within_bound UINT_MOD l_np_bare )) (PreH32 : (list_within_bound UINT_MOD l_cur )) (PreH33 : (list_within_bound UINT_MOD l_done )) (PreH34 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH35 : (0 <= carry)) (PreH36 : (carry <= UINT_MAX)) (PreH37 : (0 <= r)) (PreH38 : (r < d1_orig)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH40 : (shift_orig > 0)) (PreH41 : (qp0_bare = 0)) (PreH42 : (np = tp)) (PreH43 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> nn0_bare)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Znth nn l_cur 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_8_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare = 0)) (PreH33 : (np = tp)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_cur 0)) ” 
  &&  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "r" ) )) # UInt  |->_)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_8 := mpn_div_qr_1_preinv_partial_solve_wit_8_pure -> mpn_div_qr_1_preinv_partial_solve_wit_8_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_9_pure := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (np = qp0_bare)) (PreH34 : (tp = qp0_bare)) (PreH35 : (tn = 0)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0)) ”
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig > 0)) (PreH42 : (qp0_bare <> 0)) (PreH43 : (np = qp0_bare)) (PreH44 : (tp = qp0_bare)) (PreH45 : (tn = 0)) (PreH46 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0)) ” 
  &&  “ ((Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) <= UINT_MAX) ”
).

Definition mpn_div_qr_1_preinv_partial_solve_wit_9_pure_split_goal_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig > 0)) (PreH42 : (qp0_bare <> 0)) (PreH43 : (np = qp0_bare)) (PreH44 : (tp = qp0_bare)) (PreH45 : (tn = 0)) (PreH46 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0)) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_9_pure_split_goal_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig > 0)) (PreH42 : (qp0_bare <> 0)) (PreH43 : (np = qp0_bare)) (PreH44 : (tp = qp0_bare)) (PreH45 : (tn = 0)) (PreH46 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_9_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig > 0)) (PreH32 : (qp0_bare <> 0)) (PreH33 : (np = qp0_bare)) (PreH34 : (tp = qp0_bare)) (PreH35 : (tn = 0)) (PreH36 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) ,
  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0)) ” 
  &&  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (np = qp0_bare) ” 
  &&  “ (tp = qp0_bare) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ”
  &&  ((( &( "r" ) )) # UInt  |->_)
  **  (UIntArray.seg np 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_9 := mpn_div_qr_1_preinv_partial_solve_wit_9_pure -> mpn_div_qr_1_preinv_partial_solve_wit_9_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_10_pure := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (0 <= (Znth nn l_cur 0)) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_np_bare 0)) ”
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_np_bare 0)) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_np_bare 0)) ”
).

Definition mpn_div_qr_1_preinv_partial_solve_wit_10_pure_split_goal_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_np_bare 0)) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_10_pure_split_goal_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_10_pure_split_goal_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_10_pure_split_goal_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_np_bare 0)) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_10_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare <> 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (0 <= (Znth nn l_cur 0)) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_np_bare 0)) ” 
  &&  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  ((( &( "r" ) )) # UInt  |->_)
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_10 := mpn_div_qr_1_preinv_partial_solve_wit_10_pure -> mpn_div_qr_1_preinv_partial_solve_wit_10_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_11_pure := 
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (0 <= (Znth nn l_cur 0)) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_np_bare 0)) ”
) \/
(
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_np_bare 0)) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_np_bare 0)) ”
).

Definition mpn_div_qr_1_preinv_partial_solve_wit_11_pure_split_goal_1 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_np_bare 0)) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_11_pure_split_goal_2 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_11_pure_split_goal_3 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_11_pure_split_goal_4 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (shift_orig <= UINT_MAX)) (PreH2 : (r <= UINT_MAX)) (PreH3 : (shift_orig >= 0)) (PreH4 : (r >= 0)) (PreH5 : (di_orig >= 0)) (PreH6 : (d1_orig >= 0)) (PreH7 : (tn <= INT_MAX)) (PreH8 : (nn <= INT_MAX)) (PreH9 : (tn >= INT_MIN)) (PreH10 : (nn >= INT_MIN)) (PreH11 : (nn >= 0)) (PreH12 : (0 < d_orig_bare)) (PreH13 : (0 <= shift_orig)) (PreH14 : (shift_orig < 32)) (PreH15 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH16 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH17 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH18 : (d1_orig <= UINT_MAX)) (PreH19 : (0 <= d0_orig)) (PreH20 : (d0_orig <= UINT_MAX)) (PreH21 : (0 <= di_orig)) (PreH22 : (di_orig <= UINT_MAX)) (PreH23 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH24 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH25 : ((-1) <= nn)) (PreH26 : (nn < nn0_bare)) (PreH27 : (nn0_bare > 0)) (PreH28 : (nn0_bare <= INT_MAX)) (PreH29 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH30 : ((Zlength (l_cur)) = nn0_bare)) (PreH31 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH32 : (list_within_bound UINT_MOD l_np_bare )) (PreH33 : (list_within_bound UINT_MOD l_cur )) (PreH34 : (list_within_bound UINT_MOD l_done )) (PreH35 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH36 : (0 <= carry)) (PreH37 : (carry <= UINT_MAX)) (PreH38 : (0 <= r)) (PreH39 : (r < d1_orig)) (PreH40 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH41 : (shift_orig = 0)) (PreH42 : (carry = 0)) (PreH43 : (l_cur = l_np_bare)) (PreH44 : (np = np0_bare)) (PreH45 : (tp = 0)) (PreH46 : (tn = 0)) (PreH47 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "q" ) )) # UInt  |->_)
  **  ((( &( "d" ) )) # UInt  |-> d1_orig)
  **  ((( &( "di" ) )) # UInt  |-> di_orig)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0_bare)
  **  ((( &( "np_orig" ) )) # Ptr  |-> np0_bare)
  **  ((( &( "inv" ) )) # Ptr  |-> inv0_bare)
  **  ((( &( "nn" ) )) # Int  |-> nn)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "np" ) )) # Ptr  |-> np)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "tn" ) )) # Int  |-> tn)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= (Znth nn l_np_bare 0)) ”
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_11_aux := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (tn: Z) (tp: Z) (np: Z) (r: Z) (carry: Z) (qv_done: Z) (l_done: (@list Z)) (l_cur: (@list Z)) (nn: Z) (d0_orig: Z) (shift_orig: Z) (di_orig: Z) (d1_orig: Z) (PreH1 : (nn >= 0)) (PreH2 : (0 < d_orig_bare)) (PreH3 : (0 <= shift_orig)) (PreH4 : (shift_orig < 32)) (PreH5 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH6 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH7 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH8 : (d1_orig <= UINT_MAX)) (PreH9 : (0 <= d0_orig)) (PreH10 : (d0_orig <= UINT_MAX)) (PreH11 : (0 <= di_orig)) (PreH12 : (di_orig <= UINT_MAX)) (PreH13 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH14 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH15 : ((-1) <= nn)) (PreH16 : (nn < nn0_bare)) (PreH17 : (nn0_bare > 0)) (PreH18 : (nn0_bare <= INT_MAX)) (PreH19 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH20 : ((Zlength (l_cur)) = nn0_bare)) (PreH21 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH22 : (list_within_bound UINT_MOD l_np_bare )) (PreH23 : (list_within_bound UINT_MOD l_cur )) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH26 : (0 <= carry)) (PreH27 : (carry <= UINT_MAX)) (PreH28 : (0 <= r)) (PreH29 : (r < d1_orig)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH31 : (shift_orig = 0)) (PreH32 : (carry = 0)) (PreH33 : (l_cur = l_np_bare)) (PreH34 : (np = np0_bare)) (PreH35 : (tp = 0)) (PreH36 : (tn = 0)) (PreH37 : (qp0_bare = 0)) ,
  (UIntArray.full np nn0_bare l_cur )
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (0 <= (Znth nn l_cur 0)) ” 
  &&  “ ((Znth nn l_cur 0) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((Znth nn l_np_bare 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth nn l_np_bare 0)) ” 
  &&  “ (nn >= 0) ” 
  &&  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ ((-1) <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (qp0_bare = 0) ”
  &&  ((( &( "r" ) )) # UInt  |->_)
  **  (UIntArray.full np nn0_bare l_cur )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_11 := mpn_div_qr_1_preinv_partial_solve_wit_11_pure -> mpn_div_qr_1_preinv_partial_solve_wit_11_aux.

Definition mpn_div_qr_1_preinv_partial_solve_wit_12 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_done: (@list Z)) (qv_done: Z) (carry: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH35 : (shift_orig > 0)) (PreH36 : (np = qp0_bare)) (PreH37 : (tp = qp0_bare)) (PreH38 : (tn = 0)) (PreH39 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH40 : (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.seg qp0_bare 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (0 <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r_old) ” 
  &&  “ (r_old < d1_orig) ” 
  &&  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (np = qp0_bare) ” 
  &&  “ (tp = qp0_bare) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (((r_old * UINT_MOD ) + (Znth (nn - 0 ) (sublist (0) ((nn + 1 )) (l_cur)) 0) ) = ((qv * d1_orig ) + rv )) ”
  &&  (((qp0_bare + (nn * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i qp0_bare nn 0 (nn + 1 ) (sublist (0) ((nn + 1 )) (l_cur)) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_13 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_done: (@list Z)) (qv_done: Z) (carry: Z) (r_old: Z) (qv: Z) (rv: Z) (nn: Z) (np: Z) (tp: Z) (tn: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (0 <= nn)) (PreH15 : (nn < nn0_bare)) (PreH16 : (nn0_bare > 0)) (PreH17 : (nn0_bare <= INT_MAX)) (PreH18 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH19 : ((Zlength (l_cur)) = nn0_bare)) (PreH20 : ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) ))) (PreH21 : (list_within_bound UINT_MOD l_np_bare )) (PreH22 : (list_within_bound UINT_MOD l_cur )) (PreH23 : (list_within_bound UINT_MOD l_done )) (PreH24 : ((list_to_Z (UINT_MOD) (l_done)) = qv_done)) (PreH25 : (0 <= carry)) (PreH26 : (carry <= UINT_MAX)) (PreH27 : (0 <= r_old)) (PreH28 : (r_old < d1_orig)) (PreH29 : (0 <= qv)) (PreH30 : (qv <= UINT_MAX)) (PreH31 : (0 <= rv)) (PreH32 : (rv < d1_orig)) (PreH33 : (qp0_bare <> 0)) (PreH34 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) ))) (PreH35 : (shift_orig = 0)) (PreH36 : (carry = 0)) (PreH37 : (l_cur = l_np_bare)) (PreH38 : (np = np0_bare)) (PreH39 : (tp = 0)) (PreH40 : (tn = 0)) (PreH41 : (((r_old * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv ))) ,
  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.undef_seg qp0_bare 0 (nn + 1 ) )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (0 <= nn) ” 
  &&  “ (nn < nn0_bare) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_done)) = (nn0_bare - (nn + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = qv_done) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= UINT_MAX) ” 
  &&  “ (0 <= r_old) ” 
  &&  “ (r_old < d1_orig) ” 
  &&  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d1_orig) ” 
  &&  “ (qp0_bare <> 0) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = (((((list_to_Z (UINT_MOD) (l_done)) * (Z.pow (UINT_MOD) ((nn + 1 ))) ) * d1_orig ) + (r_old * (Z.pow (UINT_MOD) ((nn + 1 ))) ) ) + (list_to_Z (UINT_MOD) ((sublist (0) ((nn + 1 )) (l_cur)))) )) ” 
  &&  “ (shift_orig = 0) ” 
  &&  “ (carry = 0) ” 
  &&  “ (l_cur = l_np_bare) ” 
  &&  “ (np = np0_bare) ” 
  &&  “ (tp = 0) ” 
  &&  “ (tn = 0) ” 
  &&  “ (((r_old * UINT_MOD ) + (Znth nn l_cur 0) ) = ((qv * d1_orig ) + rv )) ”
  &&  (((qp0_bare + (nn * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i qp0_bare nn 0 (nn + 1 ) )
  **  (UIntArray.full np nn0_bare l_cur )
  **  (UIntArray.seg qp0_bare (nn + 1 ) nn0_bare l_done )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_partial_solve_wit_14 := 
forall (d_orig_bare: Z) (l_np_bare: (@list Z)) (inv0_bare: Z) (nn0_bare: Z) (np0_bare: Z) (qp0_bare: Z) (shift_orig: Z) (d1_orig: Z) (d0_orig: Z) (di_orig: Z) (l_cur: (@list Z)) (l_q: (@list Z)) (qv: Z) (carry: Z) (tmp_val: Z) (tmp_len: Z) (nn: Z) (r: Z) (np: Z) (tp: Z) (PreH1 : (0 < d_orig_bare)) (PreH2 : (0 <= shift_orig)) (PreH3 : (shift_orig < 32)) (PreH4 : (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) ))) (PreH5 : ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d1_orig)) (PreH7 : (d1_orig <= UINT_MAX)) (PreH8 : (0 <= d0_orig)) (PreH9 : (d0_orig <= UINT_MAX)) (PreH10 : (0 <= di_orig)) (PreH11 : (di_orig <= UINT_MAX)) (PreH12 : (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH13 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) ))) (PreH14 : (nn = (-1))) (PreH15 : (nn0_bare > 0)) (PreH16 : (nn0_bare <= INT_MAX)) (PreH17 : ((Zlength (l_np_bare)) = nn0_bare)) (PreH18 : ((Zlength (l_cur)) = nn0_bare)) (PreH19 : ((Zlength (l_q)) = nn0_bare)) (PreH20 : (list_within_bound UINT_MOD l_np_bare )) (PreH21 : (list_within_bound UINT_MOD l_cur )) (PreH22 : (list_within_bound UINT_MOD l_q )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH24 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r ))) (PreH25 : (0 <= r)) (PreH26 : (r < d1_orig)) (PreH27 : (shift_orig > 0)) (PreH28 : (qp0_bare = 0)) (PreH29 : (np = tp)) (PreH30 : (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) ))) (PreH31 : (0 <= tmp_len)) (PreH32 : (tmp_len <= nn0_bare)) (PreH33 : (nn0_bare <> 0)) ,
  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
|--
  “ (0 < d_orig_bare) ” 
  &&  “ (0 <= shift_orig) ” 
  &&  “ (shift_orig < 32) ” 
  &&  “ (d1_orig = (d_orig_bare * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ ((d_orig_bare * (Z.pow (2) (shift_orig)) ) < UINT_MOD) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_orig) ” 
  &&  “ (d1_orig <= UINT_MAX) ” 
  &&  “ (0 <= d0_orig) ” 
  &&  “ (d0_orig <= UINT_MAX) ” 
  &&  “ (0 <= di_orig) ” 
  &&  “ (di_orig <= UINT_MAX) ” 
  &&  “ (((di_orig + UINT_MOD ) * (UINT_MOD * d1_orig ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_orig + UINT_MOD ) + 1 ) * (UINT_MOD * d1_orig ) )) ” 
  &&  “ (nn = (-1)) ” 
  &&  “ (nn0_bare > 0) ” 
  &&  “ (nn0_bare <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn0_bare) ” 
  &&  “ ((Zlength (l_cur)) = nn0_bare) ” 
  &&  “ ((Zlength (l_q)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (list_within_bound UINT_MOD l_cur ) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((qv * d1_orig ) + r )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < d1_orig) ” 
  &&  “ (shift_orig > 0) ” 
  &&  “ (qp0_bare = 0) ” 
  &&  “ (np = tp) ” 
  &&  “ (((carry * (Z.pow (UINT_MOD) (nn0_bare)) ) + (list_to_Z (UINT_MOD) (l_cur)) ) = ((list_to_Z (UINT_MOD) (l_np_bare)) * (Z.pow (2) (shift_orig)) )) ” 
  &&  “ (0 <= tmp_len) ” 
  &&  “ (tmp_len <= nn0_bare) ” 
  &&  “ (nn0_bare <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD tp tmp_val tmp_len )
  **  (UIntArray.undef_seg tp tmp_len nn0_bare )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_orig)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_orig)
.

Definition mpn_div_qr_1_preinv_derive_optional_by_bare := 
forall (inv_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig_optional: Z) (l_np_optional: (@list Z)) (inv0_optional: Z) (nn0_optional: Z) (np0_optional: Z) (qp0_optional: Z) ,
  “ (qp0_optional = qp_pre) ” 
  &&  “ (np0_optional = np_pre) ” 
  &&  “ (nn0_optional = nn_pre) ” 
  &&  “ (inv0_optional = inv_pre) ” 
  &&  “ (nn_pre > 0) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_optional)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np_optional ) ”
  &&  (optional_q_undef qp_pre nn_pre )
  **  (UIntArray.full np_pre nn_pre l_np_optional )
  **  (store_div_inverse inv_pre 1 d_orig_optional )
|--
EX (qp0_bare: Z) (np0_bare: Z) (nn0_bare: Z) (inv0_bare: Z) (l_np_bare: (@list Z)) (d_orig_bare: Z) ,
  ((“ (qp0_bare = qp_pre) ” 
  &&  “ (np0_bare = np_pre) ” 
  &&  “ (nn0_bare = nn_pre) ” 
  &&  “ (inv0_bare = inv_pre) ” 
  &&  “ (nn_pre > 0) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp_pre <> 0) ” 
  &&  “ (qp_pre <> np_pre) ”
  &&  (UIntArray.undef_full qp_pre nn_pre )
  **  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 1 d_orig_bare ))
  ||
  (“ (qp0_bare = qp_pre) ” 
  &&  “ (np0_bare = np_pre) ” 
  &&  “ (nn0_bare = nn_pre) ” 
  &&  “ (inv0_bare = inv_pre) ” 
  &&  “ (nn_pre > 0) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np_bare)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np_bare ) ” 
  &&  “ (qp_pre = 0) ”
  &&  (UIntArray.full np_pre nn_pre l_np_bare )
  **  (store_div_inverse inv_pre 1 d_orig_bare )))
  **
  (((EX qv_2 l_q_2 retval_2,
  “ ((Zlength (l_q_2)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + retval_2 )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < d_orig_bare) ” 
  &&  “ (qp0_bare <> 0) ”
  &&  (UIntArray.full qp0_bare nn0_bare l_q_2 )
  **  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (store_div_inverse inv0_bare 1 d_orig_bare ))
  ||
  (EX qv_2 l_q_2 retval_2,
  “ ((Zlength (l_q_2)) = nn0_bare) ” 
  &&  “ (list_within_bound UINT_MOD l_q_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_bare)) = ((qv_2 * d_orig_bare ) + retval_2 )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < d_orig_bare) ” 
  &&  “ (qp0_bare = 0) ”
  &&  (UIntArray.full np0_bare nn0_bare l_np_bare )
  **  (store_div_inverse inv0_bare 1 d_orig_bare )))
  -*
  (EX qv l_q retval,
  “ ((Zlength (l_q)) = nn0_optional) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np_optional)) = ((qv * d_orig_optional ) + retval )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < d_orig_optional) ”
  &&  (optional_q_full qp0_optional nn0_optional l_q )
  **  (UIntArray.full np0_optional nn0_optional l_np_optional )
  **  (store_div_inverse inv0_optional 1 d_orig_optional )))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_1 : mpn_div_qr_1_preinv_safety_wit_1.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_2 : mpn_div_qr_1_preinv_safety_wit_2.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_3 : mpn_div_qr_1_preinv_safety_wit_3.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_4 : mpn_div_qr_1_preinv_safety_wit_4.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_5 : mpn_div_qr_1_preinv_safety_wit_5.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_6 : mpn_div_qr_1_preinv_safety_wit_6.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_7 : mpn_div_qr_1_preinv_safety_wit_7.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_8 : mpn_div_qr_1_preinv_safety_wit_8.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_9 : mpn_div_qr_1_preinv_safety_wit_9.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_10 : mpn_div_qr_1_preinv_safety_wit_10.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_11 : mpn_div_qr_1_preinv_safety_wit_11.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_12 : mpn_div_qr_1_preinv_safety_wit_12.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_13 : mpn_div_qr_1_preinv_safety_wit_13.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_14 : mpn_div_qr_1_preinv_safety_wit_14.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_15 : mpn_div_qr_1_preinv_safety_wit_15.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_16 : mpn_div_qr_1_preinv_safety_wit_16.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_17 : mpn_div_qr_1_preinv_safety_wit_17.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_18 : mpn_div_qr_1_preinv_safety_wit_18.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_19 : mpn_div_qr_1_preinv_safety_wit_19.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_20 : mpn_div_qr_1_preinv_safety_wit_20.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_21 : mpn_div_qr_1_preinv_safety_wit_21.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_22 : mpn_div_qr_1_preinv_safety_wit_22.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_23 : mpn_div_qr_1_preinv_safety_wit_23.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_24 : mpn_div_qr_1_preinv_safety_wit_24.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_25 : mpn_div_qr_1_preinv_safety_wit_25.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_26 : mpn_div_qr_1_preinv_safety_wit_26.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_27 : mpn_div_qr_1_preinv_safety_wit_27.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_28 : mpn_div_qr_1_preinv_safety_wit_28.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_29 : mpn_div_qr_1_preinv_safety_wit_29.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_30 : mpn_div_qr_1_preinv_safety_wit_30.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_31 : mpn_div_qr_1_preinv_safety_wit_31.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_32 : mpn_div_qr_1_preinv_safety_wit_32.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_33 : mpn_div_qr_1_preinv_safety_wit_33.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_34 : mpn_div_qr_1_preinv_safety_wit_34.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_35 : mpn_div_qr_1_preinv_safety_wit_35.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_36 : mpn_div_qr_1_preinv_safety_wit_36.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_37 : mpn_div_qr_1_preinv_safety_wit_37.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_38 : mpn_div_qr_1_preinv_safety_wit_38.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_39 : mpn_div_qr_1_preinv_safety_wit_39.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_40 : mpn_div_qr_1_preinv_safety_wit_40.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_41 : mpn_div_qr_1_preinv_safety_wit_41.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_42 : mpn_div_qr_1_preinv_safety_wit_42.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_43 : mpn_div_qr_1_preinv_safety_wit_43.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_44 : mpn_div_qr_1_preinv_safety_wit_44.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_45 : mpn_div_qr_1_preinv_safety_wit_45.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_46 : mpn_div_qr_1_preinv_safety_wit_46.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_47 : mpn_div_qr_1_preinv_safety_wit_47.
Axiom proof_of_mpn_div_qr_1_preinv_safety_wit_48 : mpn_div_qr_1_preinv_safety_wit_48.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_1_1 : mpn_div_qr_1_preinv_entail_wit_1_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_1_2 : mpn_div_qr_1_preinv_entail_wit_1_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_2_1 : mpn_div_qr_1_preinv_entail_wit_2_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_2_2 : mpn_div_qr_1_preinv_entail_wit_2_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_3_1 : mpn_div_qr_1_preinv_entail_wit_3_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_3_2 : mpn_div_qr_1_preinv_entail_wit_3_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_3_3 : mpn_div_qr_1_preinv_entail_wit_3_3.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_3_4 : mpn_div_qr_1_preinv_entail_wit_3_4.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_4_1 : mpn_div_qr_1_preinv_entail_wit_4_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_4_2 : mpn_div_qr_1_preinv_entail_wit_4_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_5_1 : mpn_div_qr_1_preinv_entail_wit_5_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_5_2 : mpn_div_qr_1_preinv_entail_wit_5_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_5_3 : mpn_div_qr_1_preinv_entail_wit_5_3.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_5_4 : mpn_div_qr_1_preinv_entail_wit_5_4.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_6_1 : mpn_div_qr_1_preinv_entail_wit_6_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_6_2 : mpn_div_qr_1_preinv_entail_wit_6_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_6_3 : mpn_div_qr_1_preinv_entail_wit_6_3.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_6_4 : mpn_div_qr_1_preinv_entail_wit_6_4.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_7_1 : mpn_div_qr_1_preinv_entail_wit_7_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_7_2 : mpn_div_qr_1_preinv_entail_wit_7_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_7_3 : mpn_div_qr_1_preinv_entail_wit_7_3.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_7_4 : mpn_div_qr_1_preinv_entail_wit_7_4.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_8_1 : mpn_div_qr_1_preinv_entail_wit_8_1.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_8_2 : mpn_div_qr_1_preinv_entail_wit_8_2.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_8_3 : mpn_div_qr_1_preinv_entail_wit_8_3.
Axiom proof_of_mpn_div_qr_1_preinv_entail_wit_8_4 : mpn_div_qr_1_preinv_entail_wit_8_4.
Axiom proof_of_mpn_div_qr_1_preinv_return_wit_1 : mpn_div_qr_1_preinv_return_wit_1.
Axiom proof_of_mpn_div_qr_1_preinv_return_wit_2 : mpn_div_qr_1_preinv_return_wit_2.
Axiom proof_of_mpn_div_qr_1_preinv_return_wit_3 : mpn_div_qr_1_preinv_return_wit_3.
Axiom proof_of_mpn_div_qr_1_preinv_return_wit_4 : mpn_div_qr_1_preinv_return_wit_4.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_1_pure : mpn_div_qr_1_preinv_partial_solve_wit_1_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_1 : mpn_div_qr_1_preinv_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_2_pure : mpn_div_qr_1_preinv_partial_solve_wit_2_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_2 : mpn_div_qr_1_preinv_partial_solve_wit_2.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_3_pure : mpn_div_qr_1_preinv_partial_solve_wit_3_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_3 : mpn_div_qr_1_preinv_partial_solve_wit_3.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_4 : mpn_div_qr_1_preinv_partial_solve_wit_4.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_5 : mpn_div_qr_1_preinv_partial_solve_wit_5.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_6 : mpn_div_qr_1_preinv_partial_solve_wit_6.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_7 : mpn_div_qr_1_preinv_partial_solve_wit_7.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_8_pure : mpn_div_qr_1_preinv_partial_solve_wit_8_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_8 : mpn_div_qr_1_preinv_partial_solve_wit_8.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_9_pure : mpn_div_qr_1_preinv_partial_solve_wit_9_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_9 : mpn_div_qr_1_preinv_partial_solve_wit_9.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_10_pure : mpn_div_qr_1_preinv_partial_solve_wit_10_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_10 : mpn_div_qr_1_preinv_partial_solve_wit_10.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_11_pure : mpn_div_qr_1_preinv_partial_solve_wit_11_pure.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_11 : mpn_div_qr_1_preinv_partial_solve_wit_11.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_12 : mpn_div_qr_1_preinv_partial_solve_wit_12.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_13 : mpn_div_qr_1_preinv_partial_solve_wit_13.
Axiom proof_of_mpn_div_qr_1_preinv_partial_solve_wit_14 : mpn_div_qr_1_preinv_partial_solve_wit_14.
Axiom proof_of_mpn_div_qr_1_preinv_derive_optional_by_bare : mpn_div_qr_1_preinv_derive_optional_by_bare.

End VC_Correct.
