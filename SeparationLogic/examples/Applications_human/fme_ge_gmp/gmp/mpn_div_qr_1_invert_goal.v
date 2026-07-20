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

(*----- Function mpn_div_qr_1_invert -----*)

Definition mpn_div_qr_1_invert_safety_wit_1 := 
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (0 < d_pre)) (PreH2 : (d_pre <= UINT_MAX)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH6 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (shift <= 31) ” 
  &&  “ (0 <= shift) ”
.

Definition mpn_div_qr_1_invert_safety_wit_2 := 
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (0 < d_pre)) (PreH2 : (d_pre <= UINT_MAX)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH6 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_1_invert_entail_wit_1 := 
(
forall (d_pre: Z) (inv_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (retval)) ))) (PreH4 : ((d_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < d_pre)) (PreH6 : (d_pre <= UINT_MAX)) ,
  (div_inverse_slot inv_pre )
|--
  “ (0 < d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (retval)) )) ” 
  &&  “ ((d_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
) \/
(
forall (d_pre: Z) (inv_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (retval)) ))) (PreH4 : ((d_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < d_pre)) (PreH6 : (d_pre <= UINT_MAX)) ,
  (div_inverse_slot inv_pre )
|--
  EX (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (0 < d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (retval)) )) ” 
  &&  “ ((d_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> x_4)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> x_3)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> x_2)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> x)
).

Definition mpn_div_qr_1_invert_return_wit_1 := 
(
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (((retval + UINT_MOD ) * ((UINT_MOD * (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) ) + 0 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH4 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval + UINT_MOD ) + 1 ) * ((UINT_MOD * (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) ) + 0 ) ))) (PreH5 : (0 < d_pre)) (PreH6 : (d_pre <= UINT_MAX)) (PreH7 : (0 <= shift)) (PreH8 : (shift < 32)) (PreH9 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH10 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval)
|--
  (store_div_inverse inv_pre 1 d_pre )
) \/
(
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) <= UINT_MAX)) (PreH2 : (shift <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) >= 0)) (PreH5 : (shift >= 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (((retval + UINT_MOD ) * ((UINT_MOD * (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) ) + 0 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH9 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval + UINT_MOD ) + 1 ) * ((UINT_MOD * (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) ) + 0 ) ))) (PreH10 : (0 < d_pre)) (PreH11 : (d_pre <= UINT_MAX)) (PreH12 : (0 <= shift)) (PreH13 : (shift < 32)) (PreH14 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH15 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval)
|--
  (store_div_inverse inv_pre 1 d_pre )
).

Definition mpn_div_qr_1_invert_return_wit_1_split_goal_spatial := 
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) <= UINT_MAX)) (PreH2 : (shift <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) >= 0)) (PreH5 : (shift >= 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (((retval + UINT_MOD ) * ((UINT_MOD * (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) ) + 0 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH9 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval + UINT_MOD ) + 1 ) * ((UINT_MOD * (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) ) + 0 ) ))) (PreH10 : (0 < d_pre)) (PreH11 : (d_pre <= UINT_MAX)) (PreH12 : (0 <= shift)) (PreH13 : (shift < 32)) (PreH14 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH15 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval)
|--
  (store_div_inverse inv_pre 1 d_pre )
.

Definition mpn_div_qr_1_invert_partial_solve_wit_1_pure := 
forall (d_pre: Z) (inv_pre: Z) (PreH1 : (0 < d_pre)) (PreH2 : (d_pre <= UINT_MAX)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 < d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ”
.

Definition mpn_div_qr_1_invert_partial_solve_wit_1_aux := 
forall (d_pre: Z) (inv_pre: Z) (PreH1 : (0 < d_pre)) (PreH2 : (d_pre <= UINT_MAX)) ,
  (div_inverse_slot inv_pre )
|--
  “ (0 < d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 < d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ”
  &&  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_1_invert_partial_solve_wit_1 := mpn_div_qr_1_invert_partial_solve_wit_1_pure -> mpn_div_qr_1_invert_partial_solve_wit_1_aux.

Definition mpn_div_qr_1_invert_partial_solve_wit_2_pure := 
(
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (0 < d_pre)) (PreH2 : (d_pre <= UINT_MAX)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH6 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32))) ”
) \/
(
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) <= UINT_MAX)) (PreH2 : (shift <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) >= 0)) (PreH4 : (shift >= 0)) (PreH5 : (d_pre >= 0)) (PreH6 : (0 < d_pre)) (PreH7 : (d_pre <= UINT_MAX)) (PreH8 : (0 <= shift)) (PreH9 : (shift < 32)) (PreH10 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH11 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32))) ”
).

Definition mpn_div_qr_1_invert_partial_solve_wit_2_pure_split_goal_1 := 
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) <= UINT_MAX)) (PreH2 : (shift <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) >= 0)) (PreH4 : (shift >= 0)) (PreH5 : (d_pre >= 0)) (PreH6 : (0 < d_pre)) (PreH7 : (d_pre <= UINT_MAX)) (PreH8 : (0 <= shift)) (PreH9 : (shift < 32)) (PreH10 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH11 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32))) ”
.

Definition mpn_div_qr_1_invert_partial_solve_wit_2_aux := 
forall (d_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (0 < d_pre)) (PreH2 : (d_pre <= UINT_MAX)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) ))) (PreH6 : ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32))) ” 
  &&  “ (0 < d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d_pre * (Z.pow (2) (shift)) )) ” 
  &&  “ ((d_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32))) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> (unsigned_last_nbits ((Z.shiftl d_pre shift)) (32)))
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_1_invert_partial_solve_wit_2 := mpn_div_qr_1_invert_partial_solve_wit_2_pure -> mpn_div_qr_1_invert_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_1_invert_safety_wit_1 : mpn_div_qr_1_invert_safety_wit_1.
Axiom proof_of_mpn_div_qr_1_invert_safety_wit_2 : mpn_div_qr_1_invert_safety_wit_2.
Axiom proof_of_mpn_div_qr_1_invert_entail_wit_1 : mpn_div_qr_1_invert_entail_wit_1.
Axiom proof_of_mpn_div_qr_1_invert_return_wit_1 : mpn_div_qr_1_invert_return_wit_1.
Axiom proof_of_mpn_div_qr_1_invert_partial_solve_wit_1_pure : mpn_div_qr_1_invert_partial_solve_wit_1_pure.
Axiom proof_of_mpn_div_qr_1_invert_partial_solve_wit_1 : mpn_div_qr_1_invert_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_1_invert_partial_solve_wit_2_pure : mpn_div_qr_1_invert_partial_solve_wit_2_pure.
Axiom proof_of_mpn_div_qr_1_invert_partial_solve_wit_2 : mpn_div_qr_1_invert_partial_solve_wit_2.

End VC_Correct.
