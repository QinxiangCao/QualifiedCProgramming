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

(*----- Function mpn_div_qr_invert -----*)

Definition mpn_div_qr_invert_safety_wit_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre > 0)) (PreH2 : (dn_pre <= INT_MAX)) (PreH3 : ((Zlength (l_dp)) = dn_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH5 : ((last (l_dp) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l_dp )) ,
  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_invert_safety_wit_2 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_invert_safety_wit_3 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_invert_safety_wit_4 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_invert_safety_wit_5 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_invert_safety_wit_6 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  ((( &( "d0" ) )) # UInt  |->_)
  **  ((( &( "d1" ) )) # UInt  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((dn_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dn_pre - 1 )) ”
.

Definition mpn_div_qr_invert_safety_wit_7 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  ((( &( "d0" ) )) # UInt  |->_)
  **  ((( &( "d1" ) )) # UInt  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_div_qr_invert_safety_wit_8 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((dn_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dn_pre - 2 )) ”
.

Definition mpn_div_qr_invert_safety_wit_9 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |->_)
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_invert_safety_wit_10 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH4 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (dn_pre <> 2)) (PreH6 : (dn_pre <> 1)) (PreH7 : (dn_pre > 0)) (PreH8 : (dn_pre <= INT_MAX)) (PreH9 : ((Zlength (l_dp)) = dn_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH11 : ((last (l_dp) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_invert_safety_wit_11 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((32 - retval ) <= 31) ” 
  &&  “ (0 <= (32 - retval )) ”
.

Definition mpn_div_qr_invert_safety_wit_12 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (retval <= 31) ” 
  &&  “ (0 <= retval) ”
.

Definition mpn_div_qr_invert_safety_wit_13 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_div_qr_invert_safety_wit_14 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((32 - retval ) <= 31) ” 
  &&  “ (0 <= (32 - retval )) ”
.

Definition mpn_div_qr_invert_safety_wit_15 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((dn_pre - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dn_pre - 3 )) ”
.

Definition mpn_div_qr_invert_safety_wit_16 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (retval <= 31) ” 
  &&  “ (0 <= retval) ”
.

Definition mpn_div_qr_invert_safety_wit_17 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition mpn_div_qr_invert_safety_wit_18 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_div_qr_invert_entail_wit_1 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (PreH1 : (dn_pre > 0)) (PreH2 : (dn_pre <= INT_MAX)) ,
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (div_inverse_slot inv_pre )
|--
  EX (l_dp: (@list Z)) ,
  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (PreH1 : (dn_pre > 0)) (PreH2 : (dn_pre <= INT_MAX)) ,
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (div_inverse_slot inv_pre )
|--
  EX (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z)  (l_dp: (@list Z)) ,
  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> x_4)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> x_3)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> x_2)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> x)
  **  (UIntArray.full dp_pre dn_pre l_dp )
).

Definition mpn_div_qr_invert_entail_wit_2 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp_2: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp_2)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d)) (PreH6 : ((last (l_dp_2) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp_2 )) ,
  (UIntArray.full dp_pre dn_pre l_dp_2 )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  EX (l_dp: (@list Z)) ,
  “ (dn_pre = 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
) \/
(
forall (dn_pre: Z) (inv_pre: Z) (d: Z) (l_dp_2: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp_2)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d)) (PreH6 : ((last (l_dp_2) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp_2 )) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  (div_inverse_slot inv_pre )
).

Definition mpn_div_qr_invert_entail_wit_2_split_goal_spatial := 
forall (dn_pre: Z) (inv_pre: Z) (d: Z) (l_dp_2: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp_2)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d)) (PreH6 : ((last (l_dp_2) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp_2 )) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_invert_entail_wit_3 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (store_div_inverse inv_pre 1 (Znth 0 l_dp 0) )
  **  (UIntArray.full dp_pre dn_pre l_dp )
|--
  “ (dn_pre = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (store_div_inverse inv_pre 1 (Znth 0 l_dp 0) )
  **  (UIntArray.full dp_pre dn_pre l_dp )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
).

Definition mpn_div_qr_invert_entail_wit_3_split_goal_spatial := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (store_div_inverse inv_pre 1 (Znth 0 l_dp 0) )
  **  (UIntArray.full dp_pre dn_pre l_dp )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_entail_wit_4 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp_2: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp_2)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d)) (PreH7 : ((last (l_dp_2) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp_2 )) ,
  (UIntArray.full dp_pre dn_pre l_dp_2 )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  EX (l_dp: (@list Z)) ,
  “ (dn_pre = 2) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
) \/
(
forall (dn_pre: Z) (inv_pre: Z) (d: Z) (l_dp_2: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp_2)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d)) (PreH7 : ((last (l_dp_2) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp_2 )) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  (div_inverse_slot inv_pre )
).

Definition mpn_div_qr_invert_entail_wit_4_split_goal_spatial := 
forall (dn_pre: Z) (inv_pre: Z) (d: Z) (l_dp_2: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp_2)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d)) (PreH7 : ((last (l_dp_2) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp_2 )) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_invert_entail_wit_5 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (store_div_inverse inv_pre 2 (((Znth 1 l_dp 0) * UINT_MOD ) + (Znth 0 l_dp 0) ) )
  **  (UIntArray.full dp_pre dn_pre l_dp )
|--
  “ (dn_pre = 2) ”
  &&  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (store_div_inverse inv_pre 2 (((Znth 1 l_dp 0) * UINT_MOD ) + (Znth 0 l_dp 0) ) )
  **  (UIntArray.full dp_pre dn_pre l_dp )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
).

Definition mpn_div_qr_invert_entail_wit_5_split_goal_spatial := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (store_div_inverse inv_pre 2 (((Znth 1 l_dp 0) * UINT_MOD ) + (Znth 0 l_dp 0) ) )
  **  (UIntArray.full dp_pre dn_pre l_dp )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_entail_wit_6_1 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= UINT_MAX)) (PreH3 : (((retval_2 + UINT_MOD ) * ((UINT_MOD * (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) ) + (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH4 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) ) + (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) ) ))) (PreH5 : (retval > 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval < 32)) (PreH8 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH9 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH10 : (dn_pre <> 2)) (PreH11 : (dn_pre <> 1)) (PreH12 : (dn_pre > 0)) (PreH13 : (dn_pre <= INT_MAX)) (PreH14 : ((Zlength (l_dp)) = dn_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH16 : ((last (l_dp) (1)) >= 1)) (PreH17 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval_2)
|--
  “ (dn_pre > 2) ”
  &&  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "d1" ) )) # UInt  |->_)
  **  ((( &( "d0" ) )) # UInt  |->_)
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval_2 >= 0)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) >= 0)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= UINT_MAX)) (PreH10 : (((retval_2 + UINT_MOD ) * ((UINT_MOD * (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) ) + (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) ) + (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) ) ))) (PreH12 : (retval > 0)) (PreH13 : (0 <= retval)) (PreH14 : (retval < 32)) (PreH15 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH16 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH17 : (dn_pre <> 2)) (PreH18 : (dn_pre <> 1)) (PreH19 : (dn_pre > 0)) (PreH20 : (dn_pre <= INT_MAX)) (PreH21 : ((Zlength (l_dp)) = dn_pre)) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH23 : ((last (l_dp) (1)) >= 1)) (PreH24 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval_2)
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
).

Definition mpn_div_qr_invert_entail_wit_6_1_split_goal_spatial := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval_2 >= 0)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) >= 0)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= UINT_MAX)) (PreH10 : (((retval_2 + UINT_MOD ) * ((UINT_MOD * (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) ) + (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) ) + (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) ) ))) (PreH12 : (retval > 0)) (PreH13 : (0 <= retval)) (PreH14 : (retval < 32)) (PreH15 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH16 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH17 : (dn_pre <> 2)) (PreH18 : (dn_pre <> 1)) (PreH19 : (dn_pre > 0)) (PreH20 : (dn_pre <= INT_MAX)) (PreH21 : ((Zlength (l_dp)) = dn_pre)) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH23 : ((last (l_dp) (1)) >= 1)) (PreH24 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval_2)
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_entail_wit_6_2 := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= UINT_MAX)) (PreH3 : (((retval_2 + UINT_MOD ) * ((UINT_MOD * (Znth (dn_pre - 1 ) l_dp 0) ) + (Znth (dn_pre - 2 ) l_dp 0) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH4 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (dn_pre - 1 ) l_dp 0) ) + (Znth (dn_pre - 2 ) l_dp 0) ) ))) (PreH5 : (retval <= 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval < 32)) (PreH8 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH9 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH10 : (dn_pre <> 2)) (PreH11 : (dn_pre <> 1)) (PreH12 : (dn_pre > 0)) (PreH13 : (dn_pre <= INT_MAX)) (PreH14 : ((Zlength (l_dp)) = dn_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH16 : ((last (l_dp) (1)) >= 1)) (PreH17 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval_2)
|--
  “ (dn_pre > 2) ”
  &&  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "d1" ) )) # UInt  |->_)
  **  ((( &( "d0" ) )) # UInt  |->_)
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX)) (PreH2 : ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval_2 >= 0)) (PreH5 : ((Znth (dn_pre - 2 ) l_dp 0) >= 0)) (PreH6 : ((Znth (dn_pre - 1 ) l_dp 0) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= UINT_MAX)) (PreH10 : (((retval_2 + UINT_MOD ) * ((UINT_MOD * (Znth (dn_pre - 1 ) l_dp 0) ) + (Znth (dn_pre - 2 ) l_dp 0) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (dn_pre - 1 ) l_dp 0) ) + (Znth (dn_pre - 2 ) l_dp 0) ) ))) (PreH12 : (retval <= 0)) (PreH13 : (0 <= retval)) (PreH14 : (retval < 32)) (PreH15 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH16 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH17 : (dn_pre <> 2)) (PreH18 : (dn_pre <> 1)) (PreH19 : (dn_pre > 0)) (PreH20 : (dn_pre <= INT_MAX)) (PreH21 : ((Zlength (l_dp)) = dn_pre)) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH23 : ((last (l_dp) (1)) >= 1)) (PreH24 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval_2)
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
).

Definition mpn_div_qr_invert_entail_wit_6_2_split_goal_spatial := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX)) (PreH2 : ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval_2 >= 0)) (PreH5 : ((Znth (dn_pre - 2 ) l_dp 0) >= 0)) (PreH6 : ((Znth (dn_pre - 1 ) l_dp 0) >= 0)) (PreH7 : (retval >= 0)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= UINT_MAX)) (PreH10 : (((retval_2 + UINT_MOD ) * ((UINT_MOD * (Znth (dn_pre - 1 ) l_dp 0) ) + (Znth (dn_pre - 2 ) l_dp 0) ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval_2 + UINT_MOD ) + 1 ) * ((UINT_MOD * (Znth (dn_pre - 1 ) l_dp 0) ) + (Znth (dn_pre - 2 ) l_dp 0) ) ))) (PreH12 : (retval <= 0)) (PreH13 : (0 <= retval)) (PreH14 : (retval < 32)) (PreH15 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH16 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH17 : (dn_pre <> 2)) (PreH18 : (dn_pre <> 1)) (PreH19 : (dn_pre > 0)) (PreH20 : (dn_pre <= INT_MAX)) (PreH21 : ((Zlength (l_dp)) = dn_pre)) (PreH22 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH23 : ((last (l_dp) (1)) >= 1)) (PreH24 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval_2)
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_return_wit_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (PreH1 : (dn_pre = 1)) ,
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_return_wit_2 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (PreH1 : (dn_pre = 2)) ,
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_return_wit_3 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (PreH1 : (dn_pre > 2)) ,
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
|--
  (mpd_store_Z_compact UINT_MOD dp_pre d dn_pre )
  **  (store_div_inverse inv_pre dn_pre d )
.

Definition mpn_div_qr_invert_partial_solve_wit_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ (dn_pre = 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (((dp_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth 0 l_dp 0))
  **  (UIntArray.missing_i dp_pre 0 0 dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_invert_partial_solve_wit_2_pure := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 0 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 < (Znth 0 l_dp 0)) ”
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 < (Znth 0 l_dp 0)) ” 
  &&  “ ((Znth 0 l_dp 0) <= UINT_MAX) ”
).

Definition mpn_div_qr_invert_partial_solve_wit_2_pure_split_goal_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 < (Znth 0 l_dp 0)) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_2_pure_split_goal_2 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 0 l_dp 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_2_aux := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 1)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 0 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 < (Znth 0 l_dp 0)) ” 
  &&  “ (dn_pre = 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (div_inverse_slot inv_pre )
  **  (UIntArray.full dp_pre dn_pre l_dp )
.

Definition mpn_div_qr_invert_partial_solve_wit_2 := mpn_div_qr_invert_partial_solve_wit_2_pure -> mpn_div_qr_invert_partial_solve_wit_2_aux.

Definition mpn_div_qr_invert_partial_solve_wit_3 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ (dn_pre = 2) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (((dp_pre + (1 * sizeof(UINT)))) # UInt  |-> (Znth 1 l_dp 0))
  **  (UIntArray.missing_i dp_pre 1 0 dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_invert_partial_solve_wit_4 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ (dn_pre = 2) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (((dp_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth 0 l_dp 0))
  **  (UIntArray.missing_i dp_pre 0 0 dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_invert_partial_solve_wit_5_pure := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 0 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth 0 l_dp 0)) ” 
  &&  “ ((Znth 1 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 < (Znth 1 l_dp 0)) ”
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 2)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 < (Znth 1 l_dp 0)) ” 
  &&  “ ((Znth 1 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth 0 l_dp 0)) ” 
  &&  “ ((Znth 0 l_dp 0) <= UINT_MAX) ”
).

Definition mpn_div_qr_invert_partial_solve_wit_5_pure_split_goal_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 2)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 < (Znth 1 l_dp 0)) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_5_pure_split_goal_2 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 2)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 1 l_dp 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_5_pure_split_goal_3 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 2)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 <= (Znth 0 l_dp 0)) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_5_pure_split_goal_4 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre >= INT_MIN)) (PreH2 : (dn_pre = 2)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 0 l_dp 0) <= UINT_MAX) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_5_aux := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre = 2)) (PreH2 : (dn_pre > 0)) (PreH3 : (dn_pre <= INT_MAX)) (PreH4 : ((Zlength (l_dp)) = dn_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH6 : ((last (l_dp) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  (div_inverse_slot inv_pre )
|--
  “ ((Znth 0 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth 0 l_dp 0)) ” 
  &&  “ ((Znth 1 l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 < (Znth 1 l_dp 0)) ” 
  &&  “ (dn_pre = 2) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (div_inverse_slot inv_pre )
  **  (UIntArray.full dp_pre dn_pre l_dp )
.

Definition mpn_div_qr_invert_partial_solve_wit_5 := mpn_div_qr_invert_partial_solve_wit_5_pure -> mpn_div_qr_invert_partial_solve_wit_5_aux.

Definition mpn_div_qr_invert_partial_solve_wit_6 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (dn_pre <> 2) ” 
  &&  “ (dn_pre <> 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (((dp_pre + ((dn_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  (UIntArray.missing_i dp_pre (dn_pre - 1 ) 0 dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_invert_partial_solve_wit_7 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (dn_pre <> 2) ” 
  &&  “ (dn_pre <> 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (((dp_pre + ((dn_pre - 2 ) * sizeof(UINT)))) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  (UIntArray.missing_i dp_pre (dn_pre - 2 ) 0 dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_invert_partial_solve_wit_8_pure := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 < (Znth (dn_pre - 1 ) l_dp 0)) ”
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX)) (PreH2 : ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX)) (PreH3 : ((Znth (dn_pre - 1 ) l_dp 0) >= 0)) (PreH4 : ((Znth (dn_pre - 2 ) l_dp 0) >= 0)) (PreH5 : (dn_pre >= INT_MIN)) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 < (Znth (dn_pre - 1 ) l_dp 0)) ”
).

Definition mpn_div_qr_invert_partial_solve_wit_8_pure_split_goal_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX)) (PreH2 : ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX)) (PreH3 : ((Znth (dn_pre - 1 ) l_dp 0) >= 0)) (PreH4 : ((Znth (dn_pre - 2 ) l_dp 0) >= 0)) (PreH5 : (dn_pre >= INT_MIN)) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 < (Znth (dn_pre - 1 ) l_dp 0)) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_8_aux := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (PreH1 : (dn_pre <> 2)) (PreH2 : (dn_pre <> 1)) (PreH3 : (dn_pre > 0)) (PreH4 : (dn_pre <= INT_MAX)) (PreH5 : ((Zlength (l_dp)) = dn_pre)) (PreH6 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH7 : ((last (l_dp) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 < (Znth (dn_pre - 1 ) l_dp 0)) ” 
  &&  “ (dn_pre <> 2) ” 
  &&  “ (dn_pre <> 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_invert_partial_solve_wit_8 := mpn_div_qr_invert_partial_solve_wit_8_pure -> mpn_div_qr_invert_partial_solve_wit_8_aux.

Definition mpn_div_qr_invert_partial_solve_wit_9 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (retval > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) )) ” 
  &&  “ (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ” 
  &&  “ (dn_pre <> 2) ” 
  &&  “ (dn_pre <> 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (((dp_pre + ((dn_pre - 3 ) * sizeof(UINT)))) # UInt  |-> (Znth (dn_pre - 3 ) l_dp 0))
  **  (UIntArray.missing_i dp_pre (dn_pre - 3 ) 0 dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_invert_partial_solve_wit_10_pure := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) <= UINT_MAX) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval )))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval )))) ”
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) >= 0)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) >= 0)) (PreH7 : (dn_pre >= INT_MIN)) (PreH8 : (retval > 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval < 32)) (PreH11 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH12 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH13 : (dn_pre <> 2)) (PreH14 : (dn_pre <> 1)) (PreH15 : (dn_pre > 0)) (PreH16 : (dn_pre <= INT_MAX)) (PreH17 : ((Zlength (l_dp)) = dn_pre)) (PreH18 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH19 : ((last (l_dp) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval )))) ”
).

Definition mpn_div_qr_invert_partial_solve_wit_10_pure_split_goal_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) >= 0)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) >= 0)) (PreH7 : (dn_pre >= INT_MIN)) (PreH8 : (retval > 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval < 32)) (PreH11 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH12 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH13 : (dn_pre <> 2)) (PreH14 : (dn_pre <> 1)) (PreH15 : (dn_pre > 0)) (PreH16 : (dn_pre <= INT_MAX)) (PreH17 : ((Zlength (l_dp)) = dn_pre)) (PreH18 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH19 : ((last (l_dp) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval )))) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_10_aux := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))) <= UINT_MAX) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval )))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval )))) ” 
  &&  “ (retval > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) )) ” 
  &&  “ (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ” 
  &&  “ (dn_pre <> 2) ” 
  &&  “ (dn_pre <> 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 1 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 2 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (dn_pre - 2 ) l_dp 0) retval)) (32)) (Z.shiftr (Znth (dn_pre - 3 ) l_dp 0) (32 - retval ))))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_invert_partial_solve_wit_10 := mpn_div_qr_invert_partial_solve_wit_10_pure -> mpn_div_qr_invert_partial_solve_wit_10_aux.

Definition mpn_div_qr_invert_partial_solve_wit_11_pure := 
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (dn_pre - 2 ) l_dp 0)) ” 
  &&  “ ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (dn_pre - 1 ) l_dp 0)) ”
) \/
(
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX)) (PreH3 : ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((Znth (dn_pre - 1 ) l_dp 0) >= 0)) (PreH6 : ((Znth (dn_pre - 2 ) l_dp 0) >= 0)) (PreH7 : (dn_pre >= INT_MIN)) (PreH8 : (retval <= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval < 32)) (PreH11 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH12 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH13 : (dn_pre <> 2)) (PreH14 : (dn_pre <> 1)) (PreH15 : (dn_pre > 0)) (PreH16 : (dn_pre <= INT_MAX)) (PreH17 : ((Zlength (l_dp)) = dn_pre)) (PreH18 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH19 : ((last (l_dp) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (Znth (dn_pre - 1 ) l_dp 0)) ”
).

Definition mpn_div_qr_invert_partial_solve_wit_11_pure_split_goal_1 := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX)) (PreH3 : ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((Znth (dn_pre - 1 ) l_dp 0) >= 0)) (PreH6 : ((Znth (dn_pre - 2 ) l_dp 0) >= 0)) (PreH7 : (dn_pre >= INT_MIN)) (PreH8 : (retval <= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval < 32)) (PreH11 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH12 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH13 : (dn_pre <> 2)) (PreH14 : (dn_pre <> 1)) (PreH15 : (dn_pre > 0)) (PreH16 : (dn_pre <= INT_MAX)) (PreH17 : ((Zlength (l_dp)) = dn_pre)) (PreH18 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH19 : ((last (l_dp) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((( &( "d0" ) )) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((( &( "d1" ) )) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (Znth (dn_pre - 1 ) l_dp 0)) ”
.

Definition mpn_div_qr_invert_partial_solve_wit_11_aux := 
forall (dn_pre: Z) (dp_pre: Z) (inv_pre: Z) (d: Z) (l_dp: (@list Z)) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ))) (PreH5 : (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH6 : (dn_pre <> 2)) (PreH7 : (dn_pre <> 1)) (PreH8 : (dn_pre > 0)) (PreH9 : (dn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_dp)) = dn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_dp)) = d)) (PreH12 : ((last (l_dp) (1)) >= 1)) (PreH13 : (list_within_bound UINT_MOD l_dp )) ,
  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((Znth (dn_pre - 2 ) l_dp 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (dn_pre - 2 ) l_dp 0)) ” 
  &&  “ ((Znth (dn_pre - 1 ) l_dp 0) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Znth (dn_pre - 1 ) l_dp 0)) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= ((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) )) ” 
  &&  “ (((Znth (dn_pre - 1 ) l_dp 0) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ” 
  &&  “ (dn_pre <> 2) ” 
  &&  “ (dn_pre <> 1) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_dp)) = dn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ”
  &&  (UIntArray.full dp_pre dn_pre l_dp )
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> retval)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (Znth (dn_pre - 1 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> (Znth (dn_pre - 2 ) l_dp 0))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_invert_partial_solve_wit_11 := mpn_div_qr_invert_partial_solve_wit_11_pure -> mpn_div_qr_invert_partial_solve_wit_11_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_invert_safety_wit_1 : mpn_div_qr_invert_safety_wit_1.
Axiom proof_of_mpn_div_qr_invert_safety_wit_2 : mpn_div_qr_invert_safety_wit_2.
Axiom proof_of_mpn_div_qr_invert_safety_wit_3 : mpn_div_qr_invert_safety_wit_3.
Axiom proof_of_mpn_div_qr_invert_safety_wit_4 : mpn_div_qr_invert_safety_wit_4.
Axiom proof_of_mpn_div_qr_invert_safety_wit_5 : mpn_div_qr_invert_safety_wit_5.
Axiom proof_of_mpn_div_qr_invert_safety_wit_6 : mpn_div_qr_invert_safety_wit_6.
Axiom proof_of_mpn_div_qr_invert_safety_wit_7 : mpn_div_qr_invert_safety_wit_7.
Axiom proof_of_mpn_div_qr_invert_safety_wit_8 : mpn_div_qr_invert_safety_wit_8.
Axiom proof_of_mpn_div_qr_invert_safety_wit_9 : mpn_div_qr_invert_safety_wit_9.
Axiom proof_of_mpn_div_qr_invert_safety_wit_10 : mpn_div_qr_invert_safety_wit_10.
Axiom proof_of_mpn_div_qr_invert_safety_wit_11 : mpn_div_qr_invert_safety_wit_11.
Axiom proof_of_mpn_div_qr_invert_safety_wit_12 : mpn_div_qr_invert_safety_wit_12.
Axiom proof_of_mpn_div_qr_invert_safety_wit_13 : mpn_div_qr_invert_safety_wit_13.
Axiom proof_of_mpn_div_qr_invert_safety_wit_14 : mpn_div_qr_invert_safety_wit_14.
Axiom proof_of_mpn_div_qr_invert_safety_wit_15 : mpn_div_qr_invert_safety_wit_15.
Axiom proof_of_mpn_div_qr_invert_safety_wit_16 : mpn_div_qr_invert_safety_wit_16.
Axiom proof_of_mpn_div_qr_invert_safety_wit_17 : mpn_div_qr_invert_safety_wit_17.
Axiom proof_of_mpn_div_qr_invert_safety_wit_18 : mpn_div_qr_invert_safety_wit_18.
Axiom proof_of_mpn_div_qr_invert_entail_wit_1 : mpn_div_qr_invert_entail_wit_1.
Axiom proof_of_mpn_div_qr_invert_entail_wit_2 : mpn_div_qr_invert_entail_wit_2.
Axiom proof_of_mpn_div_qr_invert_entail_wit_3 : mpn_div_qr_invert_entail_wit_3.
Axiom proof_of_mpn_div_qr_invert_entail_wit_4 : mpn_div_qr_invert_entail_wit_4.
Axiom proof_of_mpn_div_qr_invert_entail_wit_5 : mpn_div_qr_invert_entail_wit_5.
Axiom proof_of_mpn_div_qr_invert_entail_wit_6_1 : mpn_div_qr_invert_entail_wit_6_1.
Axiom proof_of_mpn_div_qr_invert_entail_wit_6_2 : mpn_div_qr_invert_entail_wit_6_2.
Axiom proof_of_mpn_div_qr_invert_return_wit_1 : mpn_div_qr_invert_return_wit_1.
Axiom proof_of_mpn_div_qr_invert_return_wit_2 : mpn_div_qr_invert_return_wit_2.
Axiom proof_of_mpn_div_qr_invert_return_wit_3 : mpn_div_qr_invert_return_wit_3.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_1 : mpn_div_qr_invert_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_2_pure : mpn_div_qr_invert_partial_solve_wit_2_pure.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_2 : mpn_div_qr_invert_partial_solve_wit_2.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_3 : mpn_div_qr_invert_partial_solve_wit_3.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_4 : mpn_div_qr_invert_partial_solve_wit_4.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_5_pure : mpn_div_qr_invert_partial_solve_wit_5_pure.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_5 : mpn_div_qr_invert_partial_solve_wit_5.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_6 : mpn_div_qr_invert_partial_solve_wit_6.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_7 : mpn_div_qr_invert_partial_solve_wit_7.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_8_pure : mpn_div_qr_invert_partial_solve_wit_8_pure.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_8 : mpn_div_qr_invert_partial_solve_wit_8.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_9 : mpn_div_qr_invert_partial_solve_wit_9.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_10_pure : mpn_div_qr_invert_partial_solve_wit_10_pure.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_10 : mpn_div_qr_invert_partial_solve_wit_10.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_11_pure : mpn_div_qr_invert_partial_solve_wit_11_pure.
Axiom proof_of_mpn_div_qr_invert_partial_solve_wit_11 : mpn_div_qr_invert_partial_solve_wit_11.

End VC_Correct.
