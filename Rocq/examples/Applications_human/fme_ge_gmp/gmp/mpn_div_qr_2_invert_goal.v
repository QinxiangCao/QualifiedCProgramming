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

(*----- Function mpn_div_qr_2_invert -----*)

Definition mpn_div_qr_2_invert_safety_wit_1 := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (0 < d1_pre)) (PreH2 : (d1_pre <= UINT_MAX)) (PreH3 : (0 <= d0_pre)) (PreH4 : (d0_pre <= UINT_MAX)) (PreH5 : (0 <= shift)) (PreH6 : (shift < 32)) (PreH7 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH8 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_div_qr_2_invert_safety_wit_2 := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((32 - shift ) <= 31) ” 
  &&  “ (0 <= (32 - shift )) ”
.

Definition mpn_div_qr_2_invert_safety_wit_3 := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (shift <= 31) ” 
  &&  “ (0 <= shift) ”
.

Definition mpn_div_qr_2_invert_safety_wit_4 := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_div_qr_2_invert_safety_wit_5 := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))))
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ (shift <= 31) ” 
  &&  “ (0 <= shift) ”
.

Definition mpn_div_qr_2_invert_entail_wit_1 := 
(
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (retval)) ))) (PreH4 : ((d1_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < d1_pre)) (PreH6 : (d1_pre <= UINT_MAX)) (PreH7 : (0 <= d0_pre)) (PreH8 : (d0_pre <= UINT_MAX)) ,
  (div_inverse_slot inv_pre )
|--
  “ (0 < d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (retval)) )) ” 
  &&  “ ((d1_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
) \/
(
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (retval)) ))) (PreH4 : ((d1_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < d1_pre)) (PreH6 : (d1_pre <= UINT_MAX)) (PreH7 : (0 <= d0_pre)) (PreH8 : (d0_pre <= UINT_MAX)) ,
  (div_inverse_slot inv_pre )
|--
  EX (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (0 < d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (retval)) )) ” 
  &&  “ ((d1_pre * (Z.pow (2) (retval)) ) < (Z.pow (2) (32))) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> x_4)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> x_3)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> x_2)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> x)
).

Definition mpn_div_qr_2_invert_entail_wit_2_1 := 
(
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  EX (inv_shift: Z) ,
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) )) ” 
  &&  “ ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32))) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))) * UINT_MOD ) + (unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)) ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift )))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)) <= UINT_MAX) ” 
  &&  “ (inv_shift = shift) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
) \/
(
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))) <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift )))) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))) * UINT_MOD ) + (unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)) ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) )) ”
  &&  emp
).

Definition mpn_div_qr_2_invert_entail_wit_2_1_split_goal_1 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)) <= UINT_MAX)
.

Definition mpn_div_qr_2_invert_entail_wit_2_1_split_goal_2 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  (0 <= (unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)))
.

Definition mpn_div_qr_2_invert_entail_wit_2_1_split_goal_3 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))) <= UINT_MAX)
.

Definition mpn_div_qr_2_invert_entail_wit_2_1_split_goal_4 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((UINT_MOD ÷ 2 ) <= (Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))))
.

Definition mpn_div_qr_2_invert_entail_wit_2_1_split_goal_5 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift > 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((((Z.lor (unsigned_last_nbits ((Z.shiftl d1_pre shift)) (32)) (Z.shiftr d0_pre (32 - shift ))) * UINT_MOD ) + (unsigned_last_nbits ((Z.shiftl d0_pre shift)) (32)) ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))
.

Definition mpn_div_qr_2_invert_entail_wit_2_2 := 
(
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (shift: Z) (PreH1 : (shift <= 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  EX (inv_shift: Z) ,
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) )) ” 
  &&  “ ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32))) ” 
  &&  “ (((d1_pre * UINT_MOD ) + d0_pre ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (inv_shift = shift) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |->_)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
) \/
(
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift <= 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  TT && emp 
|--
  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (((d1_pre * UINT_MOD ) + d0_pre ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) )) ”
  &&  emp
).

Definition mpn_div_qr_2_invert_entail_wit_2_2_split_goal_1 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift <= 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  ((UINT_MOD ÷ 2 ) <= d1_pre)
.

Definition mpn_div_qr_2_invert_entail_wit_2_2_split_goal_2 := 
forall (d0_pre: Z) (d1_pre: Z) (shift: Z) (PreH1 : (shift <= 0)) (PreH2 : (0 < d1_pre)) (PreH3 : (d1_pre <= UINT_MAX)) (PreH4 : (0 <= d0_pre)) (PreH5 : (d0_pre <= UINT_MAX)) (PreH6 : (0 <= shift)) (PreH7 : (shift < 32)) (PreH8 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH9 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) ,
  (((d1_pre * UINT_MOD ) + d0_pre ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))
.

Definition mpn_div_qr_2_invert_return_wit_1 := 
(
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (nd1: Z) (nd0: Z) (shift: Z) (inv_shift: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (((retval + UINT_MOD ) * ((UINT_MOD * nd1 ) + nd0 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH4 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval + UINT_MOD ) + 1 ) * ((UINT_MOD * nd1 ) + nd0 ) ))) (PreH5 : (0 <= shift)) (PreH6 : (shift < 32)) (PreH7 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH8 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) (PreH9 : (((nd1 * UINT_MOD ) + nd0 ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= nd1)) (PreH11 : (nd1 <= UINT_MAX)) (PreH12 : (0 <= nd0)) (PreH13 : (nd0 <= UINT_MAX)) (PreH14 : (inv_shift = shift)) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> nd1)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> nd0)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval)
|--
  (store_div_inverse inv_pre 2 ((d1_pre * UINT_MOD ) + d0_pre ) )
) \/
(
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (nd1: Z) (nd0: Z) (shift: Z) (inv_shift: Z) (retval: Z) (PreH1 : (inv_shift <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (nd0 >= 0)) (PreH4 : (nd1 >= 0)) (PreH5 : (inv_shift >= 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (((retval + UINT_MOD ) * ((UINT_MOD * nd1 ) + nd0 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH9 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval + UINT_MOD ) + 1 ) * ((UINT_MOD * nd1 ) + nd0 ) ))) (PreH10 : (0 <= shift)) (PreH11 : (shift < 32)) (PreH12 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH13 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) (PreH14 : (((nd1 * UINT_MOD ) + nd0 ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))) (PreH15 : ((UINT_MOD ÷ 2 ) <= nd1)) (PreH16 : (nd1 <= UINT_MAX)) (PreH17 : (0 <= nd0)) (PreH18 : (nd0 <= UINT_MAX)) (PreH19 : (inv_shift = shift)) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> nd1)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> nd0)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval)
|--
  (store_div_inverse inv_pre 2 ((d1_pre * UINT_MOD ) + d0_pre ) )
).

Definition mpn_div_qr_2_invert_return_wit_1_split_goal_spatial := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (nd1: Z) (nd0: Z) (shift: Z) (inv_shift: Z) (retval: Z) (PreH1 : (inv_shift <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (nd0 >= 0)) (PreH4 : (nd1 >= 0)) (PreH5 : (inv_shift >= 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (((retval + UINT_MOD ) * ((UINT_MOD * nd1 ) + nd0 ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH9 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((retval + UINT_MOD ) + 1 ) * ((UINT_MOD * nd1 ) + nd0 ) ))) (PreH10 : (0 <= shift)) (PreH11 : (shift < 32)) (PreH12 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH13 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) (PreH14 : (((nd1 * UINT_MOD ) + nd0 ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))) (PreH15 : ((UINT_MOD ÷ 2 ) <= nd1)) (PreH16 : (nd1 <= UINT_MAX)) (PreH17 : (0 <= nd0)) (PreH18 : (nd0 <= UINT_MAX)) (PreH19 : (inv_shift = shift)) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> nd1)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> nd0)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |-> retval)
|--
  (store_div_inverse inv_pre 2 ((d1_pre * UINT_MOD ) + d0_pre ) )
.

Definition mpn_div_qr_2_invert_partial_solve_wit_1_pure := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (PreH1 : (0 < d1_pre)) (PreH2 : (d1_pre <= UINT_MAX)) (PreH3 : (0 <= d0_pre)) (PreH4 : (d0_pre <= UINT_MAX)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  (div_inverse_slot inv_pre )
|--
  “ (0 < d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ”
.

Definition mpn_div_qr_2_invert_partial_solve_wit_1_aux := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (PreH1 : (0 < d1_pre)) (PreH2 : (d1_pre <= UINT_MAX)) (PreH3 : (0 <= d0_pre)) (PreH4 : (d0_pre <= UINT_MAX)) ,
  (div_inverse_slot inv_pre )
|--
  “ (0 < d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 < d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ”
  &&  (div_inverse_slot inv_pre )
.

Definition mpn_div_qr_2_invert_partial_solve_wit_1 := mpn_div_qr_2_invert_partial_solve_wit_1_pure -> mpn_div_qr_2_invert_partial_solve_wit_1_aux.

Definition mpn_div_qr_2_invert_partial_solve_wit_2_pure := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (nd1: Z) (nd0: Z) (shift: Z) (inv_shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH4 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) (PreH5 : (((nd1 * UINT_MOD ) + nd0 ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))) (PreH6 : ((UINT_MOD ÷ 2 ) <= nd1)) (PreH7 : (nd1 <= UINT_MAX)) (PreH8 : (0 <= nd0)) (PreH9 : (nd0 <= UINT_MAX)) (PreH10 : (inv_shift = shift)) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "d1" ) )) # UInt  |-> nd1)
  **  ((( &( "d0" ) )) # UInt  |-> nd0)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> nd1)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> nd0)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= nd1) ” 
  &&  “ (nd1 <= UINT_MAX) ” 
  &&  “ (0 <= nd0) ” 
  &&  “ (nd0 <= UINT_MAX) ”
.

Definition mpn_div_qr_2_invert_partial_solve_wit_2_aux := 
forall (d0_pre: Z) (d1_pre: Z) (inv_pre: Z) (nd1: Z) (nd0: Z) (shift: Z) (inv_shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) ))) (PreH4 : ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32)))) (PreH5 : (((nd1 * UINT_MOD ) + nd0 ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) ))) (PreH6 : ((UINT_MOD ÷ 2 ) <= nd1)) (PreH7 : (nd1 <= UINT_MAX)) (PreH8 : (0 <= nd0)) (PreH9 : (nd0 <= UINT_MAX)) (PreH10 : (inv_shift = shift)) ,
  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> nd1)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> nd0)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
|--
  “ ((UINT_MOD ÷ 2 ) <= nd1) ” 
  &&  “ (nd1 <= UINT_MAX) ” 
  &&  “ (0 <= nd0) ” 
  &&  “ (nd0 <= UINT_MAX) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (d1_pre * (Z.pow (2) (shift)) )) ” 
  &&  “ ((d1_pre * (Z.pow (2) (shift)) ) < (Z.pow (2) (32))) ” 
  &&  “ (((nd1 * UINT_MOD ) + nd0 ) = (((d1_pre * UINT_MOD ) + d0_pre ) * (Z.pow (2) (shift)) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= nd1) ” 
  &&  “ (nd1 <= UINT_MAX) ” 
  &&  “ (0 <= nd0) ” 
  &&  “ (nd0 <= UINT_MAX) ” 
  &&  “ (inv_shift = shift) ”
  &&  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "shift")) # UInt  |-> inv_shift)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d1")) # UInt  |-> nd1)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "d0")) # UInt  |-> nd0)
  **  ((&((inv_pre)  # "gmp_div_inverse" ->ₛ "di")) # UInt  |->_)
.

Definition mpn_div_qr_2_invert_partial_solve_wit_2 := mpn_div_qr_2_invert_partial_solve_wit_2_pure -> mpn_div_qr_2_invert_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_div_qr_2_invert_safety_wit_1 : mpn_div_qr_2_invert_safety_wit_1.
Axiom proof_of_mpn_div_qr_2_invert_safety_wit_2 : mpn_div_qr_2_invert_safety_wit_2.
Axiom proof_of_mpn_div_qr_2_invert_safety_wit_3 : mpn_div_qr_2_invert_safety_wit_3.
Axiom proof_of_mpn_div_qr_2_invert_safety_wit_4 : mpn_div_qr_2_invert_safety_wit_4.
Axiom proof_of_mpn_div_qr_2_invert_safety_wit_5 : mpn_div_qr_2_invert_safety_wit_5.
Axiom proof_of_mpn_div_qr_2_invert_entail_wit_1 : mpn_div_qr_2_invert_entail_wit_1.
Axiom proof_of_mpn_div_qr_2_invert_entail_wit_2_1 : mpn_div_qr_2_invert_entail_wit_2_1.
Axiom proof_of_mpn_div_qr_2_invert_entail_wit_2_2 : mpn_div_qr_2_invert_entail_wit_2_2.
Axiom proof_of_mpn_div_qr_2_invert_return_wit_1 : mpn_div_qr_2_invert_return_wit_1.
Axiom proof_of_mpn_div_qr_2_invert_partial_solve_wit_1_pure : mpn_div_qr_2_invert_partial_solve_wit_1_pure.
Axiom proof_of_mpn_div_qr_2_invert_partial_solve_wit_1 : mpn_div_qr_2_invert_partial_solve_wit_1.
Axiom proof_of_mpn_div_qr_2_invert_partial_solve_wit_2_pure : mpn_div_qr_2_invert_partial_solve_wit_2_pure.
Axiom proof_of_mpn_div_qr_2_invert_partial_solve_wit_2 : mpn_div_qr_2_invert_partial_solve_wit_2.

End VC_Correct.
