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

(*----- Function mpn_div_qr -----*)

Definition mpn_div_qr_safety_wit_1 := 
forall (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (nn0 = nn_pre)) (PreH6 : (dn0 = dn_pre)) (PreH7 : (dn_pre > 0)) (PreH8 : (dn_pre <= nn_pre)) (PreH9 : (nn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_np)) = nn_pre)) (PreH11 : (list_within_bound UINT_MOD l_np )) ,
  (div_inverse_slot retval )
  **  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "inv" ) )) # Ptr  |-> retval)
  **  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (mpd_store_Z_compact UINT_MOD dp_pre d_orig dn_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_safety_wit_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp = 0)) (PreH3 : (dn0 > 0)) (PreH4 : (dn0 <= nn0)) (PreH5 : (nn0 <= INT_MAX)) (PreH6 : ((Zlength (l_np)) = nn0)) (PreH7 : (list_within_bound UINT_MOD l_np )) (PreH8 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH9 : (dn0 = 1)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_safety_wit_3 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp = 0)) (PreH3 : (dn0 > 0)) (PreH4 : (dn0 <= nn0)) (PreH5 : (nn0 <= INT_MAX)) (PreH6 : ((Zlength (l_np)) = nn0)) (PreH7 : (list_within_bound UINT_MOD l_np )) (PreH8 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH9 : (dn0 <> 1)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpn_div_qr_safety_wit_4 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dn0 > 2)) (PreH2 : (dp0 = dp_pre)) (PreH3 : (tp = 0)) (PreH4 : (dn0 > 0)) (PreH5 : (dn0 <= nn0)) (PreH6 : (nn0 <= INT_MAX)) (PreH7 : ((Zlength (l_np)) = nn0)) (PreH8 : (list_within_bound UINT_MOD l_np )) (PreH9 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH10 : (dn0 = 1)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ False ”
.

Definition mpn_div_qr_safety_wit_5 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dn0 > 2)) (PreH2 : (dp0 = dp_pre)) (PreH3 : (tp = 0)) (PreH4 : (dn0 > 0)) (PreH5 : (dn0 <= nn0)) (PreH6 : (nn0 <= INT_MAX)) (PreH7 : ((Zlength (l_np)) = nn0)) (PreH8 : (list_within_bound UINT_MOD l_np )) (PreH9 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH10 : (dn0 <> 1)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_safety_wit_6 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp <> 0)) (PreH18 : (dp = tp)) (PreH19 : (dn0 > 2)) (PreH20 : (tp = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  “ False ”
.

Definition mpn_div_qr_safety_wit_7 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (shift = 0)) (PreH19 : (tp <> 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ False ”
.

Definition mpn_div_qr_safety_wit_8 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (dn0 <= 2)) (PreH19 : (tp <> 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ False ”
.

Definition mpn_div_qr_entail_wit_1 := 
forall (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (qp0 = qp_pre)) (PreH3 : (np0 = np_pre)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (nn0 = nn_pre)) (PreH6 : (dn0 = dn_pre)) (PreH7 : (dn_pre > 0)) (PreH8 : (dn_pre <= nn_pre)) (PreH9 : (nn_pre <= INT_MAX)) (PreH10 : ((Zlength (l_np)) = nn_pre)) (PreH11 : (list_within_bound UINT_MOD l_np )) ,
  (div_inverse_slot retval )
  **  ((( &( "qp" ) )) # Ptr  |-> qp_pre)
  **  ((( &( "np" ) )) # Ptr  |-> np_pre)
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "dn" ) )) # Int  |-> dn_pre)
  **  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (mpd_store_Z_compact UINT_MOD dp_pre d_orig dn_pre )
|--
  “ (dp0 = dp_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot retval )
.

Definition mpn_div_qr_entail_wit_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp = 0)) (PreH3 : (dn0 > 0)) (PreH4 : (dn0 <= nn0)) (PreH5 : (nn0 <= INT_MAX)) (PreH6 : ((Zlength (l_np)) = nn0)) (PreH7 : (list_within_bound UINT_MOD l_np )) ,
  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_div_inverse inv dn0 d_orig )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
|--
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (dn0 = 1) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di))
  ||
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (dn0 <> 1) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di))
.

Definition mpn_div_qr_entail_wit_3 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (shift_2 > 0)) (PreH3 : (dn0 > 2)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (tp = 0)) (PreH6 : (dn0 > 0)) (PreH7 : (dn0 <= nn0)) (PreH8 : (nn0 <= INT_MAX)) (PreH9 : ((Zlength (l_np)) = nn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH12 : (dn0 <> 1)) ,
  (UIntArray.undef_full retval dn0 )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  EX (d1: Z)  (d0: Z)  (di: Z)  (l_dp: (@list Z))  (shift: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d_orig) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.undef_full retval dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (shift_2 > 0)) (PreH3 : (dn0 > 2)) (PreH4 : (dp0 = dp_pre)) (PreH5 : (tp = 0)) (PreH6 : (dn0 > 0)) (PreH7 : (dn0 <= nn0)) (PreH8 : (nn0 <= INT_MAX)) (PreH9 : ((Zlength (l_np)) = nn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH12 : (dn0 <> 1)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
|--
  EX (l_dp: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (1 <= shift_2) ” 
  &&  “ (shift_2 < 32) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d_orig) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 ) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
).

Definition mpn_div_qr_entail_wit_4 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (l_dp: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = dn0)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (2) (shift)) ))) (PreH4 : (dp0 = dp_pre)) (PreH5 : (tp <> 0)) (PreH6 : (dn0 > 2)) (PreH7 : (1 <= shift)) (PreH8 : (shift < 32)) (PreH9 : (dn0 <= nn0)) (PreH10 : (nn0 <= INT_MAX)) (PreH11 : ((Zlength (l_np)) = nn0)) (PreH12 : ((Zlength (l_dp)) = dn0)) (PreH13 : (list_within_bound UINT_MOD l_np )) (PreH14 : (list_within_bound UINT_MOD l_dp )) (PreH15 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH16 : ((last (l_dp) (1)) >= 1)) (PreH17 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  (UIntArray.full tp dn0 l_out )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
|--
  “ (0 = 0) ” 
  &&  “ (di <= UINT_MAX) ” 
  &&  “ (d0 <= UINT_MAX) ” 
  &&  “ (d1 <= UINT_MAX) ” 
  &&  “ (shift <= UINT_MAX) ” 
  &&  “ (di >= 0) ” 
  &&  “ (d0 >= 0) ” 
  &&  “ (d1 >= 0) ” 
  &&  “ (shift >= 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (dn0 >= INT_MIN) ” 
  &&  “ (nn0 >= INT_MIN) ” 
  &&  “ ((Zlength (l_out)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d_orig) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ”
  &&  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full tp dn0 l_out )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (l_dp: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (di <= UINT_MAX)) (PreH3 : (d0 <= UINT_MAX)) (PreH4 : (d1 <= UINT_MAX)) (PreH5 : (shift <= UINT_MAX)) (PreH6 : (retval >= 0)) (PreH7 : (di >= 0)) (PreH8 : (d0 >= 0)) (PreH9 : (d1 >= 0)) (PreH10 : (shift >= 0)) (PreH11 : (dn0 <= INT_MAX)) (PreH12 : (dn0 >= INT_MIN)) (PreH13 : (nn0 >= INT_MIN)) (PreH14 : ((Zlength (l_out)) = dn0)) (PreH15 : (list_within_bound UINT_MOD l_out )) (PreH16 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (2) (shift)) ))) (PreH17 : (dp0 = dp_pre)) (PreH18 : (tp <> 0)) (PreH19 : (dn0 > 2)) (PreH20 : (1 <= shift)) (PreH21 : (shift < 32)) (PreH22 : (dn0 <= nn0)) (PreH23 : (nn0 <= INT_MAX)) (PreH24 : ((Zlength (l_np)) = nn0)) (PreH25 : ((Zlength (l_dp)) = dn0)) (PreH26 : (list_within_bound UINT_MOD l_np )) (PreH27 : (list_within_bound UINT_MOD l_dp )) (PreH28 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH29 : ((last (l_dp) (1)) >= 1)) (PreH30 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  TT && emp 
|--
  “ (retval = 0) ”
  &&  emp
).

Definition mpn_div_qr_entail_wit_4_split_goal_1 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (l_dp: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (di <= UINT_MAX)) (PreH3 : (d0 <= UINT_MAX)) (PreH4 : (d1 <= UINT_MAX)) (PreH5 : (shift <= UINT_MAX)) (PreH6 : (retval >= 0)) (PreH7 : (di >= 0)) (PreH8 : (d0 >= 0)) (PreH9 : (d1 >= 0)) (PreH10 : (shift >= 0)) (PreH11 : (dn0 <= INT_MAX)) (PreH12 : (dn0 >= INT_MIN)) (PreH13 : (nn0 >= INT_MIN)) (PreH14 : ((Zlength (l_out)) = dn0)) (PreH15 : (list_within_bound UINT_MOD l_out )) (PreH16 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp)) * (Z.pow (2) (shift)) ))) (PreH17 : (dp0 = dp_pre)) (PreH18 : (tp <> 0)) (PreH19 : (dn0 > 2)) (PreH20 : (1 <= shift)) (PreH21 : (shift < 32)) (PreH22 : (dn0 <= nn0)) (PreH23 : (nn0 <= INT_MAX)) (PreH24 : ((Zlength (l_np)) = nn0)) (PreH25 : ((Zlength (l_dp)) = dn0)) (PreH26 : (list_within_bound UINT_MOD l_np )) (PreH27 : (list_within_bound UINT_MOD l_dp )) (PreH28 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH29 : ((last (l_dp) (1)) >= 1)) (PreH30 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  (retval = 0)
.

Definition mpn_div_qr_entail_wit_5 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (l_dp_2: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (0 = 0)) (PreH2 : (di_2 <= UINT_MAX)) (PreH3 : (d0_2 <= UINT_MAX)) (PreH4 : (d1_2 <= UINT_MAX)) (PreH5 : (shift_2 <= UINT_MAX)) (PreH6 : (di_2 >= 0)) (PreH7 : (d0_2 >= 0)) (PreH8 : (d1_2 >= 0)) (PreH9 : (shift_2 >= 0)) (PreH10 : (dn0 <= INT_MAX)) (PreH11 : (dn0 >= INT_MIN)) (PreH12 : (nn0 >= INT_MIN)) (PreH13 : ((Zlength (l_out)) = dn0)) (PreH14 : (list_within_bound UINT_MOD l_out )) (PreH15 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp_2)) * (Z.pow (2) (shift_2)) ))) (PreH16 : (dp0 = dp_pre)) (PreH17 : (tp <> 0)) (PreH18 : (dn0 > 2)) (PreH19 : (1 <= shift_2)) (PreH20 : (shift_2 < 32)) (PreH21 : (dn0 <= nn0)) (PreH22 : (nn0 <= INT_MAX)) (PreH23 : ((Zlength (l_np)) = nn0)) (PreH24 : ((Zlength (l_dp_2)) = dn0)) (PreH25 : (list_within_bound UINT_MOD l_np )) (PreH26 : (list_within_bound UINT_MOD l_dp_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d_orig)) (PreH28 : ((last (l_dp_2) (1)) >= 1)) (PreH29 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) ,
  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full tp dn0 l_out )
  **  (UIntArray.full dp0 dn0 l_dp_2 )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  EX (d1: Z)  (d0: Z)  (di: Z)  (l_norm: (@list Z))  (l_dp: (@list Z))  (shift: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (tp = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ ((Zlength (l_norm)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ (list_within_bound UINT_MOD l_norm ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d_orig) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_norm)) = (d_orig * (Z.pow (2) (shift)) )) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.full tp dn0 l_norm )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
  **  ((( &( "cy" ) )) # UInt  |->_)
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (l_dp_2: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (di_2 <= UINT_MAX)) (PreH2 : (d0_2 <= UINT_MAX)) (PreH3 : (d1_2 <= UINT_MAX)) (PreH4 : (shift_2 <= UINT_MAX)) (PreH5 : (di_2 >= 0)) (PreH6 : (d0_2 >= 0)) (PreH7 : (d1_2 >= 0)) (PreH8 : (shift_2 >= 0)) (PreH9 : (dn0 <= INT_MAX)) (PreH10 : (dn0 >= INT_MIN)) (PreH11 : (nn0 >= INT_MIN)) (PreH12 : ((Zlength (l_out)) = dn0)) (PreH13 : (list_within_bound UINT_MOD l_out )) (PreH14 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp_2)) * (Z.pow (2) (shift_2)) ))) (PreH15 : (dp0 = dp_pre)) (PreH16 : (tp <> 0)) (PreH17 : (dn0 > 2)) (PreH18 : (1 <= shift_2)) (PreH19 : (shift_2 < 32)) (PreH20 : (dn0 <= nn0)) (PreH21 : (nn0 <= INT_MAX)) (PreH22 : ((Zlength (l_np)) = nn0)) (PreH23 : ((Zlength (l_dp_2)) = dn0)) (PreH24 : (list_within_bound UINT_MOD l_np )) (PreH25 : (list_within_bound UINT_MOD l_dp_2 )) (PreH26 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d_orig)) (PreH27 : ((last (l_dp_2) (1)) >= 1)) (PreH28 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) ,
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) (l_out)) = (d_orig * (Z.pow (2) (shift_2)) )) ”
  &&  emp
).

Definition mpn_div_qr_entail_wit_5_split_goal_1 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (l_dp_2: (@list Z)) (l_out: (@list Z)) (retval: Z) (PreH1 : (di_2 <= UINT_MAX)) (PreH2 : (d0_2 <= UINT_MAX)) (PreH3 : (d1_2 <= UINT_MAX)) (PreH4 : (shift_2 <= UINT_MAX)) (PreH5 : (di_2 >= 0)) (PreH6 : (d0_2 >= 0)) (PreH7 : (d1_2 >= 0)) (PreH8 : (shift_2 >= 0)) (PreH9 : (dn0 <= INT_MAX)) (PreH10 : (dn0 >= INT_MIN)) (PreH11 : (nn0 >= INT_MIN)) (PreH12 : ((Zlength (l_out)) = dn0)) (PreH13 : (list_within_bound UINT_MOD l_out )) (PreH14 : (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (dn0)) ) ) = ((list_to_Z (UINT_MOD) (l_dp_2)) * (Z.pow (2) (shift_2)) ))) (PreH15 : (dp0 = dp_pre)) (PreH16 : (tp <> 0)) (PreH17 : (dn0 > 2)) (PreH18 : (1 <= shift_2)) (PreH19 : (shift_2 < 32)) (PreH20 : (dn0 <= nn0)) (PreH21 : (nn0 <= INT_MAX)) (PreH22 : ((Zlength (l_np)) = nn0)) (PreH23 : ((Zlength (l_dp_2)) = dn0)) (PreH24 : (list_within_bound UINT_MOD l_np )) (PreH25 : (list_within_bound UINT_MOD l_dp_2 )) (PreH26 : ((list_to_Z (UINT_MOD) (l_dp_2)) = d_orig)) (PreH27 : ((last (l_dp_2) (1)) >= 1)) (PreH28 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) ,
  ((list_to_Z (UINT_MOD) (l_out)) = (d_orig * (Z.pow (2) (shift_2)) ))
.

Definition mpn_div_qr_entail_wit_6_1 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (tp: Z) (dp_2: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp <> 0)) (PreH3 : (dp_2 = tp)) (PreH4 : (dn0 > 2)) (PreH5 : (1 <= shift_2)) (PreH6 : (shift_2 < 32)) (PreH7 : (dn0 <= nn0)) (PreH8 : (nn0 <= INT_MAX)) (PreH9 : ((Zlength (l_np)) = nn0)) (PreH10 : ((Zlength (l_dp)) = dn0)) (PreH11 : ((Zlength (l_norm)) = dn0)) (PreH12 : (list_within_bound UINT_MOD l_np )) (PreH13 : (list_within_bound UINT_MOD l_dp )) (PreH14 : (list_within_bound UINT_MOD l_norm )) (PreH15 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH16 : ((last (l_dp) (1)) >= 1)) (PreH17 : ((list_to_Z (UINT_MOD) (l_norm)) = (d_orig * (Z.pow (2) (shift_2)) ))) (PreH18 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_2)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.full dp_2 dn0 l_norm )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  EX (dp: Z)  (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ”
  &&  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (l_dp: (@list Z)) (l_norm: (@list Z)) (tp: Z) (dp_2: Z) (inv: Z) (PreH1 : (di_2 <= UINT_MAX)) (PreH2 : (d0_2 <= UINT_MAX)) (PreH3 : (d1_2 <= UINT_MAX)) (PreH4 : (shift_2 <= UINT_MAX)) (PreH5 : (di_2 >= 0)) (PreH6 : (d0_2 >= 0)) (PreH7 : (d1_2 >= 0)) (PreH8 : (shift_2 >= 0)) (PreH9 : (dp0 = dp_pre)) (PreH10 : (tp <> 0)) (PreH11 : (dp_2 = tp)) (PreH12 : (dn0 > 2)) (PreH13 : (1 <= shift_2)) (PreH14 : (shift_2 < 32)) (PreH15 : (dn0 <= nn0)) (PreH16 : (nn0 <= INT_MAX)) (PreH17 : ((Zlength (l_np)) = nn0)) (PreH18 : ((Zlength (l_dp)) = dn0)) (PreH19 : ((Zlength (l_norm)) = dn0)) (PreH20 : (list_within_bound UINT_MOD l_np )) (PreH21 : (list_within_bound UINT_MOD l_dp )) (PreH22 : (list_within_bound UINT_MOD l_norm )) (PreH23 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH24 : ((last (l_dp) (1)) >= 1)) (PreH25 : ((list_to_Z (UINT_MOD) (l_norm)) = (d_orig * (Z.pow (2) (shift_2)) ))) (PreH26 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.full dp_2 dn0 l_norm )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp_2 = tp) ” 
  &&  “ (dp_2 = tp) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dn0 > 2) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor tp inv dn0 d_orig )
).

Definition mpn_div_qr_entail_wit_6_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (PreH1 : (dn0 <= 2)) (PreH2 : (dp0 = dp_pre)) (PreH3 : (tp = 0)) (PreH4 : (dn0 > 0)) (PreH5 : (dn0 <= nn0)) (PreH6 : (nn0 <= INT_MAX)) (PreH7 : ((Zlength (l_np)) = nn0)) (PreH8 : (list_within_bound UINT_MOD l_np )) (PreH9 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH10 : (dn0 <> 1)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_6_3 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (PreH1 : (dn0 <= 2)) (PreH2 : (dp0 = dp_pre)) (PreH3 : (tp = 0)) (PreH4 : (dn0 > 0)) (PreH5 : (dn0 <= nn0)) (PreH6 : (nn0 <= INT_MAX)) (PreH7 : ((Zlength (l_np)) = nn0)) (PreH8 : (list_within_bound UINT_MOD l_np )) (PreH9 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH10 : (dn0 = 1)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_6_4 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (PreH1 : (shift_2 <= 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dp0 = dp_pre)) (PreH4 : (tp = 0)) (PreH5 : (dn0 > 0)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : (list_within_bound UINT_MOD l_np )) (PreH10 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH11 : (dn0 <> 1)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (PreH1 : (di_2 <= UINT_MAX)) (PreH2 : (d0_2 <= UINT_MAX)) (PreH3 : (d1_2 <= UINT_MAX)) (PreH4 : (shift_2 <= UINT_MAX)) (PreH5 : (di_2 >= 0)) (PreH6 : (d0_2 >= 0)) (PreH7 : (d1_2 >= 0)) (PreH8 : (shift_2 >= 0)) (PreH9 : (shift_2 <= 0)) (PreH10 : (dn0 > 2)) (PreH11 : (dp0 = dp_pre)) (PreH12 : (tp = 0)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) (PreH18 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH19 : (dn0 <> 1)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0_2)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di_2)
|--
  EX (d1: Z)  (d0: Z)  (di: Z) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig 0 d1 d0 di ) ” 
  &&  “ (tp = 0) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
).

Definition mpn_div_qr_entail_wit_7_1 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (dp_2: Z) (inv: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH2 : ((Zlength (l_rem_2)) = dn0)) (PreH3 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH4 : (list_within_bound UINT_MOD l_q_2 )) (PreH5 : (list_within_bound UINT_MOD l_rem_2 )) (PreH6 : (list_within_bound UINT_MOD l_tail_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH10 : (0 <= rv_2)) (PreH11 : (rv_2 < d_orig)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) (PreH18 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH19 : (tp <> 0)) (PreH20 : (dp_2 = tp)) (PreH21 : (dn0 > 2)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp_2 inv dn0 d_orig )
  **  ((( &( "dp" ) )) # Ptr  |-> dp_2)
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
|--
  EX (dp: Z)  (shift: Z)  (d1: Z)  (d0: Z)  (di: Z)  (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ”
  &&  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (dp_2: Z) (inv: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH2 : ((Zlength (l_rem_2)) = dn0)) (PreH3 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH4 : (list_within_bound UINT_MOD l_q_2 )) (PreH5 : (list_within_bound UINT_MOD l_rem_2 )) (PreH6 : (list_within_bound UINT_MOD l_tail_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH10 : (0 <= rv_2)) (PreH11 : (rv_2 < d_orig)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) (PreH18 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH19 : (tp <> 0)) (PreH20 : (dp_2 = tp)) (PreH21 : (dn0 > 2)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (store_preinv_divisor dp_2 inv dn0 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
|--
  EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z)  (l_q: (@list Z)) ,
  “ (dp_2 = tp) ” 
  &&  “ (dp_2 = tp) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dn0 > 2) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor tp inv dn0 d_orig )
).

Definition mpn_div_qr_entail_wit_7_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH2 : ((Zlength (l_rem_2)) = dn0)) (PreH3 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH4 : (list_within_bound UINT_MOD l_q_2 )) (PreH5 : (list_within_bound UINT_MOD l_rem_2 )) (PreH6 : (list_within_bound UINT_MOD l_tail_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH10 : (0 <= rv_2)) (PreH11 : (rv_2 < d_orig)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) (PreH18 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH19 : (tp = 0)) (PreH20 : (shift_2 = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z)  (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z)  (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_7_3 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (inv: Z) (rv_2: Z) (qv_2: Z) (l_tail_2: (@list Z)) (l_rem_2: (@list Z)) (l_q_2: (@list Z)) (PreH1 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH2 : ((Zlength (l_rem_2)) = dn0)) (PreH3 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH4 : (list_within_bound UINT_MOD l_q_2 )) (PreH5 : (list_within_bound UINT_MOD l_rem_2 )) (PreH6 : (list_within_bound UINT_MOD l_tail_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH8 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH9 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH10 : (0 <= rv_2)) (PreH11 : (rv_2 < d_orig)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (dn0 > 0)) (PreH14 : (dn0 <= nn0)) (PreH15 : (nn0 <= INT_MAX)) (PreH16 : ((Zlength (l_np)) = nn0)) (PreH17 : (list_within_bound UINT_MOD l_np )) (PreH18 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH19 : (tp = 0)) (PreH20 : (dn0 <= 2)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z)  (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (EX (shift: Z)  (d1: Z)  (d0: Z)  (di: Z)  (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_8_1 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp <> 0)) (PreH18 : (dp = tp)) (PreH19 : (dn0 > 2)) (PreH20 : (tp = 0)) ,
  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  (“ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ” 
  &&  “ (tp = 0) ”
  &&  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (“ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ” 
  &&  “ (tp = 0) ”
  &&  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_8_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (shift = 0)) (PreH19 : (tp = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  (“ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ” 
  &&  “ (tp = 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (“ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ” 
  &&  “ (tp = 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_8_3 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (dn0 <= 2)) (PreH19 : (tp = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  (“ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ” 
  &&  “ (tp = 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
  ||
  (“ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ” 
  &&  “ (tp = 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig ))
.

Definition mpn_div_qr_entail_wit_9_1 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp <> 0)) (PreH18 : (dp = tp)) (PreH19 : (dn0 > 2)) (PreH20 : (tp <> 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (tp <> 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
.

Definition mpn_div_qr_entail_wit_9_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (shift = 0)) (PreH19 : (tp <> 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp0 = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (tp <> 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
.

Definition mpn_div_qr_entail_wit_9_3 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (dn0 <= 2)) (PreH19 : (tp <> 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp0 = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (tp <> 0) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
.

Definition mpn_div_qr_entail_wit_10 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH17 : (tp <> 0)) (PreH18 : (dp = tp)) (PreH19 : (dn0 > 2)) (PreH20 : (tp <> 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  EX (di: Z)  (d0: Z)  (d1: Z)  (shift: Z)  (norm_val: Z)  (rv: Z)  (qv: Z)  (l_dp: (@list Z))  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = norm_val) ” 
  &&  “ (is_compact_Z UINT_MOD norm_val dn0 ) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (mpd_store_Z_compact UINT_MOD tp norm_val dn0 )
  **  (UIntArray.undef_seg tp dn0 dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (shift_2: Z) (d1_2: Z) (d0_2: Z) (di_2: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift_2 d1_2 d0_2 di_2 )) (PreH17 : (tp <> 0)) (PreH18 : (dp = tp)) (PreH19 : (dn0 > 2)) (PreH20 : (tp <> 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  EX (di: Z)  (d0: Z)  (d1: Z)  (shift: Z)  (l_dp: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ” 
  &&  “ (is_compact_Z UINT_MOD (list_to_Z (UINT_MOD) (l_dp)) dn0 ) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (mpd_store_Z_compact UINT_MOD tp (list_to_Z (UINT_MOD) (l_dp)) dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
).

Definition mpn_div_qr_entail_wit_11_1 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (l_dp: (@list Z)) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (norm_val: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp <> 0)) (PreH3 : (dp = tp)) (PreH4 : (dn0 > 2)) (PreH5 : (dn0 <= nn0)) (PreH6 : (nn0 <= INT_MAX)) (PreH7 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH8 : ((Zlength (l_rem_2)) = dn0)) (PreH9 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH10 : ((Zlength (l_dp)) = dn0)) (PreH11 : (list_within_bound UINT_MOD l_q_2 )) (PreH12 : (list_within_bound UINT_MOD l_rem_2 )) (PreH13 : (list_within_bound UINT_MOD l_tail_2 )) (PreH14 : (list_within_bound UINT_MOD l_dp )) (PreH15 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH16 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH17 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH18 : (0 <= rv_2)) (PreH19 : (rv_2 < d_orig)) (PreH20 : ((list_to_Z (UINT_MOD) (l_dp)) = norm_val)) (PreH21 : (is_compact_Z UINT_MOD norm_val dn0 )) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (l_dp: (@list Z)) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (norm_val: Z) (PreH1 : (di <= UINT_MAX)) (PreH2 : (d0 <= UINT_MAX)) (PreH3 : (d1 <= UINT_MAX)) (PreH4 : (shift <= UINT_MAX)) (PreH5 : (di >= 0)) (PreH6 : (d0 >= 0)) (PreH7 : (d1 >= 0)) (PreH8 : (shift >= 0)) (PreH9 : (dp0 = dp_pre)) (PreH10 : (tp <> 0)) (PreH11 : (dp = tp)) (PreH12 : (dn0 > 2)) (PreH13 : (dn0 <= nn0)) (PreH14 : (nn0 <= INT_MAX)) (PreH15 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH16 : ((Zlength (l_rem_2)) = dn0)) (PreH17 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH18 : ((Zlength (l_dp)) = dn0)) (PreH19 : (list_within_bound UINT_MOD l_q_2 )) (PreH20 : (list_within_bound UINT_MOD l_rem_2 )) (PreH21 : (list_within_bound UINT_MOD l_tail_2 )) (PreH22 : (list_within_bound UINT_MOD l_dp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH24 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH25 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH26 : (0 <= rv_2)) (PreH27 : (rv_2 < d_orig)) (PreH28 : ((list_to_Z (UINT_MOD) (l_dp)) = norm_val)) (PreH29 : (is_compact_Z UINT_MOD norm_val dn0 )) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  EX (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
).

Definition mpn_div_qr_entail_wit_11_2 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (shift = 0)) (PreH19 : (tp = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (shift = 0)) (PreH19 : (tp = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  EX (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
).

Definition mpn_div_qr_entail_wit_11_3 := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (dn0 <= 2)) (PreH19 : (tp = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) (PreH16 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH17 : (tp = 0)) (PreH18 : (dn0 <= 2)) (PreH19 : (tp = 0)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  EX (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem_2)) = dn0) ” 
  &&  “ ((Zlength (l_tail_2)) = (nn0 - dn0 )) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = (((list_to_Z (UINT_MOD) (l_q)) * d_orig ) + (list_to_Z (UINT_MOD) (l_rem_2)) )) ” 
  &&  “ (0 <= (list_to_Z (UINT_MOD) (l_rem_2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem_2)) < d_orig) ”
  &&  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
).

Definition mpn_div_qr_entail_wit_12 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
|--
  EX (rv: Z)  (qv: Z)  (l_tail: (@list Z))  (l_rem: (@list Z))  (l_q: (@list Z)) ,
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
.

Definition mpn_div_qr_return_wit_1 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q_2: (@list Z)) (l_rem_2: (@list Z)) (l_tail_2: (@list Z)) (qv_2: Z) (rv_2: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q_2)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem_2)) = dn0)) (PreH7 : ((Zlength (l_tail_2)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q_2 )) (PreH9 : (list_within_bound UINT_MOD l_rem_2 )) (PreH10 : (list_within_bound UINT_MOD l_tail_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q_2)) = qv_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem_2)) = rv_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv_2 * d_orig ) + rv_2 ))) (PreH14 : (0 <= rv_2)) (PreH15 : (rv_2 < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q_2 )
  **  (UIntArray.seg np0 0 dn0 l_rem_2 )
  **  (UIntArray.seg np0 dn0 nn0 l_tail_2 )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
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
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
.

Definition mpn_div_qr_partial_solve_wit_1 := 
forall (dn_pre: Z) (dp_pre: Z) (nn_pre: Z) (np_pre: Z) (qp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (PreH1 : (qp0 = qp_pre)) (PreH2 : (np0 = np_pre)) (PreH3 : (dp0 = dp_pre)) (PreH4 : (nn0 = nn_pre)) (PreH5 : (dn0 = dn_pre)) (PreH6 : (dn_pre > 0)) (PreH7 : (dn_pre <= nn_pre)) (PreH8 : (nn_pre <= INT_MAX)) (PreH9 : ((Zlength (l_np)) = nn_pre)) (PreH10 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (mpd_store_Z_compact UINT_MOD dp_pre d_orig dn_pre )
|--
  “ (qp0 = qp_pre) ” 
  &&  “ (np0 = np_pre) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (nn0 = nn_pre) ” 
  &&  “ (dn0 = dn_pre) ” 
  &&  “ (dn_pre > 0) ” 
  &&  “ (dn_pre <= nn_pre) ” 
  &&  “ (nn_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  (optional_q_undef qp_pre ((nn_pre - dn_pre ) + 1 ) )
  **  (UIntArray.full np_pre nn_pre l_np )
  **  (mpd_store_Z_compact UINT_MOD dp_pre d_orig dn_pre )
.

Definition mpn_div_qr_partial_solve_wit_2_pure := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp = 0)) (PreH3 : (dn0 > 0)) (PreH4 : (dn0 <= nn0)) (PreH5 : (nn0 <= INT_MAX)) (PreH6 : ((Zlength (l_np)) = nn0)) (PreH7 : (list_within_bound UINT_MOD l_np )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (div_inverse_slot inv )
|--
  “ (dn0 > 0) ” 
  &&  “ (dn0 <= INT_MAX) ”
.

Definition mpn_div_qr_partial_solve_wit_2_aux := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp = 0)) (PreH3 : (dn0 > 0)) (PreH4 : (dn0 <= nn0)) (PreH5 : (nn0 <= INT_MAX)) (PreH6 : ((Zlength (l_np)) = nn0)) (PreH7 : (list_within_bound UINT_MOD l_np )) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
|--
  “ (dn0 > 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
  &&  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
.

Definition mpn_div_qr_partial_solve_wit_2 := mpn_div_qr_partial_solve_wit_2_pure -> mpn_div_qr_partial_solve_wit_2_aux.

Definition mpn_div_qr_partial_solve_wit_3_pure := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (shift > 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dp0 = dp_pre)) (PreH4 : (tp = 0)) (PreH5 : (dn0 > 0)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : (list_within_bound UINT_MOD l_np )) (PreH10 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH11 : (dn0 <> 1)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (dn0 > 0) ”
.

Definition mpn_div_qr_partial_solve_wit_3_aux := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (shift > 0)) (PreH2 : (dn0 > 2)) (PreH3 : (dp0 = dp_pre)) (PreH4 : (tp = 0)) (PreH5 : (dn0 > 0)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : (list_within_bound UINT_MOD l_np )) (PreH10 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH11 : (dn0 <> 1)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (dn0 > 0) ” 
  &&  “ (shift > 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (dn0 <> 1) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
.

Definition mpn_div_qr_partial_solve_wit_3 := mpn_div_qr_partial_solve_wit_3_pure -> mpn_div_qr_partial_solve_wit_3_aux.

Definition mpn_div_qr_partial_solve_wit_4_pure := 
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (l_dp: (@list Z)) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp <> 0)) (PreH3 : (dn0 > 2)) (PreH4 : (1 <= shift)) (PreH5 : (shift < 32)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH13 : ((last (l_dp) (1)) >= 1)) (PreH14 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.undef_full tp dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (tp <> dp0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ (tp <> dp_pre) ”
) \/
(
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (l_dp: (@list Z)) (PreH1 : (di <= UINT_MAX)) (PreH2 : (d0 <= UINT_MAX)) (PreH3 : (d1 <= UINT_MAX)) (PreH4 : (shift <= UINT_MAX)) (PreH5 : (di >= 0)) (PreH6 : (d0 >= 0)) (PreH7 : (d1 >= 0)) (PreH8 : (shift >= 0)) (PreH9 : (dn0 <= INT_MAX)) (PreH10 : (dn0 >= INT_MIN)) (PreH11 : (nn0 >= INT_MIN)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (tp <> 0)) (PreH14 : (dn0 > 2)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (dn0 <= nn0)) (PreH18 : (nn0 <= INT_MAX)) (PreH19 : ((Zlength (l_np)) = nn0)) (PreH20 : ((Zlength (l_dp)) = dn0)) (PreH21 : (list_within_bound UINT_MOD l_np )) (PreH22 : (list_within_bound UINT_MOD l_dp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH24 : ((last (l_dp) (1)) >= 1)) (PreH25 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.undef_full tp dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (tp <> dp_pre) ” 
  &&  “ (tp <> dp_pre) ”
).

Definition mpn_div_qr_partial_solve_wit_4_pure_split_goal_1 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (l_dp: (@list Z)) (PreH1 : (di <= UINT_MAX)) (PreH2 : (d0 <= UINT_MAX)) (PreH3 : (d1 <= UINT_MAX)) (PreH4 : (shift <= UINT_MAX)) (PreH5 : (di >= 0)) (PreH6 : (d0 >= 0)) (PreH7 : (d1 >= 0)) (PreH8 : (shift >= 0)) (PreH9 : (dn0 <= INT_MAX)) (PreH10 : (dn0 >= INT_MIN)) (PreH11 : (nn0 >= INT_MIN)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (tp <> 0)) (PreH14 : (dn0 > 2)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (dn0 <= nn0)) (PreH18 : (nn0 <= INT_MAX)) (PreH19 : ((Zlength (l_np)) = nn0)) (PreH20 : ((Zlength (l_dp)) = dn0)) (PreH21 : (list_within_bound UINT_MOD l_np )) (PreH22 : (list_within_bound UINT_MOD l_dp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH24 : ((last (l_dp) (1)) >= 1)) (PreH25 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.undef_full tp dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (tp <> dp_pre) ”
.

Definition mpn_div_qr_partial_solve_wit_4_pure_split_goal_2 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (l_dp: (@list Z)) (PreH1 : (di <= UINT_MAX)) (PreH2 : (d0 <= UINT_MAX)) (PreH3 : (d1 <= UINT_MAX)) (PreH4 : (shift <= UINT_MAX)) (PreH5 : (di >= 0)) (PreH6 : (d0 >= 0)) (PreH7 : (d1 >= 0)) (PreH8 : (shift >= 0)) (PreH9 : (dn0 <= INT_MAX)) (PreH10 : (dn0 >= INT_MIN)) (PreH11 : (nn0 >= INT_MIN)) (PreH12 : (dp0 = dp_pre)) (PreH13 : (tp <> 0)) (PreH14 : (dn0 > 2)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (dn0 <= nn0)) (PreH18 : (nn0 <= INT_MAX)) (PreH19 : ((Zlength (l_np)) = nn0)) (PreH20 : ((Zlength (l_dp)) = dn0)) (PreH21 : (list_within_bound UINT_MOD l_np )) (PreH22 : (list_within_bound UINT_MOD l_dp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH24 : ((last (l_dp) (1)) >= 1)) (PreH25 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.undef_full tp dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
  **  ((( &( "cy" ) )) # UInt  |->_)
|--
  “ (tp <> dp_pre) ”
.

Definition mpn_div_qr_partial_solve_wit_4_aux := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (l_dp: (@list Z)) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp <> 0)) (PreH3 : (dn0 > 2)) (PreH4 : (1 <= shift)) (PreH5 : (shift < 32)) (PreH6 : (dn0 <= nn0)) (PreH7 : (nn0 <= INT_MAX)) (PreH8 : ((Zlength (l_np)) = nn0)) (PreH9 : ((Zlength (l_dp)) = dn0)) (PreH10 : (list_within_bound UINT_MOD l_np )) (PreH11 : (list_within_bound UINT_MOD l_dp )) (PreH12 : ((list_to_Z (UINT_MOD) (l_dp)) = d_orig)) (PreH13 : ((last (l_dp) (1)) >= 1)) (PreH14 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (UIntArray.undef_full tp dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (tp <> dp0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= INT_MAX) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ (tp <> dp_pre) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = d_orig) ” 
  &&  “ ((last (l_dp) (1)) >= 1) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ”
  &&  (UIntArray.undef_full tp dn0 )
  **  (UIntArray.full dp0 dn0 l_dp )
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
.

Definition mpn_div_qr_partial_solve_wit_4 := mpn_div_qr_partial_solve_wit_4_pure -> mpn_div_qr_partial_solve_wit_4_aux.

Definition mpn_div_qr_partial_solve_wit_5_pure := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) (PreH7 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH8 : (tp <> 0)) (PreH9 : (dp = tp)) (PreH10 : (dn0 > 2)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "dp" ) )) # Ptr  |-> dp)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp = dp) ” 
  &&  “ (inv = inv) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
.

Definition mpn_div_qr_partial_solve_wit_5_aux := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) (PreH7 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH8 : (tp <> 0)) (PreH9 : (dp = tp)) (PreH10 : (dn0 > 2)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (store_preinv_divisor dp inv dn0 d_orig )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp = dp) ” 
  &&  “ (inv = inv) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp inv dn0 d_orig )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
.

Definition mpn_div_qr_partial_solve_wit_5 := mpn_div_qr_partial_solve_wit_5_pure -> mpn_div_qr_partial_solve_wit_5_aux.

Definition mpn_div_qr_partial_solve_wit_6_pure := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) (PreH7 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH8 : (tp = 0)) (PreH9 : (shift = 0)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (inv = inv) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
.

Definition mpn_div_qr_partial_solve_wit_6_aux := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) (PreH7 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH8 : (tp = 0)) (PreH9 : (shift = 0)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (inv = inv) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (shift = 0) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
.

Definition mpn_div_qr_partial_solve_wit_6 := mpn_div_qr_partial_solve_wit_6_pure -> mpn_div_qr_partial_solve_wit_6_aux.

Definition mpn_div_qr_partial_solve_wit_7_pure := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) (PreH7 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH8 : (tp = 0)) (PreH9 : (dn0 <= 2)) ,
  ((( &( "qp" ) )) # Ptr  |-> qp0)
  **  ((( &( "np" ) )) # Ptr  |-> np0)
  **  ((( &( "nn" ) )) # Int  |-> nn0)
  **  ((( &( "dn" ) )) # Int  |-> dn0)
  **  ((( &( "tp" ) )) # Ptr  |-> tp)
  **  ((( &( "dp" ) )) # Ptr  |-> dp0)
  **  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (inv = inv) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ”
.

Definition mpn_div_qr_partial_solve_wit_7_aux := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_np)) = nn0)) (PreH6 : (list_within_bound UINT_MOD l_np )) (PreH7 : (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di )) (PreH8 : (tp = 0)) (PreH9 : (dn0 <= 2)) ,
  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
|--
  “ (qp0 = qp0) ” 
  &&  “ (np0 = np0) ” 
  &&  “ (dp0 = dp0) ” 
  &&  “ (inv = inv) ” 
  &&  “ (nn0 = nn0) ” 
  &&  “ (dn0 = dn0) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_np)) = nn0) ” 
  &&  “ (list_within_bound UINT_MOD l_np ) ” 
  &&  “ (gmp_div_inverse_valid dn0 d_orig shift d1 d0 di ) ” 
  &&  “ (tp = 0) ” 
  &&  “ (dn0 <= 2) ”
  &&  (optional_q_undef qp0 ((nn0 - dn0 ) + 1 ) )
  **  (UIntArray.full np0 nn0 l_np )
  **  (store_preinv_divisor dp0 inv dn0 d_orig )
.

Definition mpn_div_qr_partial_solve_wit_7 := mpn_div_qr_partial_solve_wit_7_pure -> mpn_div_qr_partial_solve_wit_7_aux.

Definition mpn_div_qr_partial_solve_wit_8 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (l_dp: (@list Z)) (shift: Z) (d1: Z) (d0: Z) (di: Z) (tp: Z) (dp: Z) (inv: Z) (norm_val: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (tp <> 0)) (PreH3 : (dp = tp)) (PreH4 : (dn0 > 2)) (PreH5 : (dn0 <= nn0)) (PreH6 : (nn0 <= INT_MAX)) (PreH7 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH8 : ((Zlength (l_rem)) = dn0)) (PreH9 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH10 : ((Zlength (l_dp)) = dn0)) (PreH11 : (list_within_bound UINT_MOD l_q )) (PreH12 : (list_within_bound UINT_MOD l_rem )) (PreH13 : (list_within_bound UINT_MOD l_tail )) (PreH14 : (list_within_bound UINT_MOD l_dp )) (PreH15 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH16 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH17 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH18 : (0 <= rv)) (PreH19 : (rv < d_orig)) (PreH20 : ((list_to_Z (UINT_MOD) (l_dp)) = norm_val)) (PreH21 : (is_compact_Z UINT_MOD norm_val dn0 )) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (mpd_store_Z_compact UINT_MOD tp norm_val dn0 )
  **  (UIntArray.undef_seg tp dn0 dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
|--
  “ (dp0 = dp_pre) ” 
  &&  “ (tp <> 0) ” 
  &&  “ (dp = tp) ” 
  &&  “ (dn0 > 2) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
  &&  “ ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 )) ” 
  &&  “ ((Zlength (l_rem)) = dn0) ” 
  &&  “ ((Zlength (l_tail)) = (nn0 - dn0 )) ” 
  &&  “ ((Zlength (l_dp)) = dn0) ” 
  &&  “ (list_within_bound UINT_MOD l_q ) ” 
  &&  “ (list_within_bound UINT_MOD l_rem ) ” 
  &&  “ (list_within_bound UINT_MOD l_tail ) ” 
  &&  “ (list_within_bound UINT_MOD l_dp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_q)) = qv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_rem)) = rv) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv )) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_orig) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_dp)) = norm_val) ” 
  &&  “ (is_compact_Z UINT_MOD norm_val dn0 ) ”
  &&  (mpd_store_Z_compact UINT_MOD tp norm_val dn0 )
  **  (UIntArray.undef_seg tp dn0 dn0 )
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> d1)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> d0)
  **  ((&((inv)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> di)
.

Definition mpn_div_qr_partial_solve_wit_9 := 
forall (dp_pre: Z) (d_orig: Z) (l_np: (@list Z)) (dn0: Z) (nn0: Z) (dp0: Z) (np0: Z) (qp0: Z) (l_q: (@list Z)) (l_rem: (@list Z)) (l_tail: (@list Z)) (qv: Z) (rv: Z) (inv: Z) (PreH1 : (dp0 = dp_pre)) (PreH2 : (dn0 > 0)) (PreH3 : (dn0 <= nn0)) (PreH4 : (nn0 <= INT_MAX)) (PreH5 : ((Zlength (l_q)) = ((nn0 - dn0 ) + 1 ))) (PreH6 : ((Zlength (l_rem)) = dn0)) (PreH7 : ((Zlength (l_tail)) = (nn0 - dn0 ))) (PreH8 : (list_within_bound UINT_MOD l_q )) (PreH9 : (list_within_bound UINT_MOD l_rem )) (PreH10 : (list_within_bound UINT_MOD l_tail )) (PreH11 : ((list_to_Z (UINT_MOD) (l_q)) = qv)) (PreH12 : ((list_to_Z (UINT_MOD) (l_rem)) = rv)) (PreH13 : ((list_to_Z (UINT_MOD) (l_np)) = ((qv * d_orig ) + rv ))) (PreH14 : (0 <= rv)) (PreH15 : (rv < d_orig)) ,
  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
  **  (div_inverse_slot inv )
|--
  “ (dp0 = dp_pre) ” 
  &&  “ (dn0 > 0) ” 
  &&  “ (dn0 <= nn0) ” 
  &&  “ (nn0 <= INT_MAX) ” 
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
  &&  (div_inverse_slot inv )
  **  (optional_q_full qp0 ((nn0 - dn0 ) + 1 ) l_q )
  **  (UIntArray.seg np0 0 dn0 l_rem )
  **  (UIntArray.seg np0 dn0 nn0 l_tail )
  **  (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0 )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_safety_wit_1 : mpn_div_qr_safety_wit_1.
Axiom proof_of_mpn_div_qr_safety_wit_2 : mpn_div_qr_safety_wit_2.
Axiom proof_of_mpn_div_qr_safety_wit_3 : mpn_div_qr_safety_wit_3.
Axiom proof_of_mpn_div_qr_safety_wit_4 : mpn_div_qr_safety_wit_4.
Axiom proof_of_mpn_div_qr_safety_wit_5 : mpn_div_qr_safety_wit_5.
Axiom proof_of_mpn_div_qr_safety_wit_6 : mpn_div_qr_safety_wit_6.
Axiom proof_of_mpn_div_qr_safety_wit_7 : mpn_div_qr_safety_wit_7.
Axiom proof_of_mpn_div_qr_safety_wit_8 : mpn_div_qr_safety_wit_8.
Axiom proof_of_mpn_div_qr_entail_wit_1 : mpn_div_qr_entail_wit_1.
Axiom proof_of_mpn_div_qr_entail_wit_2 : mpn_div_qr_entail_wit_2.
Axiom proof_of_mpn_div_qr_entail_wit_3 : mpn_div_qr_entail_wit_3.
Axiom proof_of_mpn_div_qr_entail_wit_4 : mpn_div_qr_entail_wit_4.
Axiom proof_of_mpn_div_qr_entail_wit_5 : mpn_div_qr_entail_wit_5.
Axiom proof_of_mpn_div_qr_entail_wit_6_1 : mpn_div_qr_entail_wit_6_1.
Axiom proof_of_mpn_div_qr_entail_wit_6_2 : mpn_div_qr_entail_wit_6_2.
Axiom proof_of_mpn_div_qr_entail_wit_6_3 : mpn_div_qr_entail_wit_6_3.
Axiom proof_of_mpn_div_qr_entail_wit_6_4 : mpn_div_qr_entail_wit_6_4.
Axiom proof_of_mpn_div_qr_entail_wit_7_1 : mpn_div_qr_entail_wit_7_1.
Axiom proof_of_mpn_div_qr_entail_wit_7_2 : mpn_div_qr_entail_wit_7_2.
Axiom proof_of_mpn_div_qr_entail_wit_7_3 : mpn_div_qr_entail_wit_7_3.
Axiom proof_of_mpn_div_qr_entail_wit_8_1 : mpn_div_qr_entail_wit_8_1.
Axiom proof_of_mpn_div_qr_entail_wit_8_2 : mpn_div_qr_entail_wit_8_2.
Axiom proof_of_mpn_div_qr_entail_wit_8_3 : mpn_div_qr_entail_wit_8_3.
Axiom proof_of_mpn_div_qr_entail_wit_9_1 : mpn_div_qr_entail_wit_9_1.
Axiom proof_of_mpn_div_qr_entail_wit_9_2 : mpn_div_qr_entail_wit_9_2.
Axiom proof_of_mpn_div_qr_entail_wit_9_3 : mpn_div_qr_entail_wit_9_3.
Axiom proof_of_mpn_div_qr_entail_wit_10 : mpn_div_qr_entail_wit_10.
Axiom proof_of_mpn_div_qr_entail_wit_11_1 : mpn_div_qr_entail_wit_11_1.
Axiom proof_of_mpn_div_qr_entail_wit_11_2 : mpn_div_qr_entail_wit_11_2.
Axiom proof_of_mpn_div_qr_entail_wit_11_3 : mpn_div_qr_entail_wit_11_3.
Axiom proof_of_mpn_div_qr_entail_wit_12 : mpn_div_qr_entail_wit_12.
Axiom proof_of_mpn_div_qr_return_wit_1 : mpn_div_qr_return_wit_1.
Axiom proof_of_mpn_div_qr_partial_solve_wit_1 : mpn_div_qr_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_partial_solve_wit_2_pure : mpn_div_qr_partial_solve_wit_2_pure.
Axiom proof_of_mpn_div_qr_partial_solve_wit_2 : mpn_div_qr_partial_solve_wit_2.
Axiom proof_of_mpn_div_qr_partial_solve_wit_3_pure : mpn_div_qr_partial_solve_wit_3_pure.
Axiom proof_of_mpn_div_qr_partial_solve_wit_3 : mpn_div_qr_partial_solve_wit_3.
Axiom proof_of_mpn_div_qr_partial_solve_wit_4_pure : mpn_div_qr_partial_solve_wit_4_pure.
Axiom proof_of_mpn_div_qr_partial_solve_wit_4 : mpn_div_qr_partial_solve_wit_4.
Axiom proof_of_mpn_div_qr_partial_solve_wit_5_pure : mpn_div_qr_partial_solve_wit_5_pure.
Axiom proof_of_mpn_div_qr_partial_solve_wit_5 : mpn_div_qr_partial_solve_wit_5.
Axiom proof_of_mpn_div_qr_partial_solve_wit_6_pure : mpn_div_qr_partial_solve_wit_6_pure.
Axiom proof_of_mpn_div_qr_partial_solve_wit_6 : mpn_div_qr_partial_solve_wit_6.
Axiom proof_of_mpn_div_qr_partial_solve_wit_7_pure : mpn_div_qr_partial_solve_wit_7_pure.
Axiom proof_of_mpn_div_qr_partial_solve_wit_7 : mpn_div_qr_partial_solve_wit_7.
Axiom proof_of_mpn_div_qr_partial_solve_wit_8 : mpn_div_qr_partial_solve_wit_8.
Axiom proof_of_mpn_div_qr_partial_solve_wit_9 : mpn_div_qr_partial_solve_wit_9.

End VC_Correct.
