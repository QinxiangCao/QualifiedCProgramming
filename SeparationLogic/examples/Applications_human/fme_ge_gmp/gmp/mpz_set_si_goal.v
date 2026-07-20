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

(*----- Function mpz_set_si -----*)

Definition mpz_set_si_safety_wit_1 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre = x0)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_set_si_safety_wit_2 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_set_si_safety_wit_3 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_set_si_safety_wit_4 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpz_set_si_safety_wit_5 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_set_si_safety_wit_6 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) (PreH3 : (same_sign old size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (cap >= 0)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_set_si_safety_wit_7 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_set_si_safety_wit_8 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ ((x_pre + 1 ) <> (INT_MIN)) ”
.

Definition mpz_set_si_safety_wit_9 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ ((x_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + 1 )) ”
.

Definition mpz_set_si_safety_wit_10 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_set_si_safety_wit_11 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_set_si_entail_wit_1 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (x_pre < 0)) (PreH4 : (x_pre = x0)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old)) (Zabs (size_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (x_pre < 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs ((-1))) <= (Z.max (1) (cap))) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
) \/
(
forall (x_pre: Z) (x0: Z) (old: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (x_pre < 0)) (PreH4 : (x_pre = x0)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old)) (Zabs (size_2)) )
|--
  EX (size: Z) ,
  “ (x_pre < 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (cap_2 >= 0) ” 
  &&  “ (cap_2 <= INT_MAX) ” 
  &&  “ ((Zabs ((-1))) <= (Z.max (1) (cap_2))) ”
  &&  (UIntArray.undef_full ptr_2 cap_2 )
).

Definition mpz_set_si_entail_wit_2 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (cap_new: Z) ,
  “ (cap_new = (Z.max (1) (cap))) ” 
  &&  “ (x_pre < 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (cap_new >= 1) ” 
  &&  “ (cap_new <= INT_MAX) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (UIntArray.undef_seg retval 0 1 )
  **  (UIntArray.undef_seg retval 1 cap_new )
) \/
(
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  “ ((Z.max (1) (cap)) <= INT_MAX) ” 
  &&  “ ((Z.max (1) (cap)) >= 1) ”
  &&  (UIntArray.undef_seg retval 0 1 )
  **  (UIntArray.undef_seg retval 1 (Z.max (1) (cap)) )
).

Definition mpz_set_si_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  “ ((Z.max (1) (cap)) <= INT_MAX) ”
.

Definition mpz_set_si_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  “ ((Z.max (1) (cap)) >= 1) ”
.

Definition mpz_set_si_entail_wit_2_split_goal_spatial := 
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  (UIntArray.undef_seg retval 0 1 )
  **  (UIntArray.undef_seg retval 1 (Z.max (1) (cap)) )
.

Definition mpz_set_si_return_wit_1 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (x_pre = x0)) ,
  (store_Z r_pre x0 )
|--
  (store_Z r_pre x0 )
.

Definition mpz_set_si_return_wit_2 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> ((-(x_pre + 1 )) + 1 ))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  (store_Z r_pre x0 )
) \/
(
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (((-(x_pre + 1 )) + 1 ) <= UINT_MAX)) (PreH2 : (((-(x_pre + 1 )) + 1 ) >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre < 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> ((-(x_pre + 1 )) + 1 ))
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ ((Zabs ((-1))) <= cap_new) ” 
  &&  “ (same_sign x0 (-1) ) ”
  &&  (UIntArray.undef_seg rp_addr_v (Zabs ((-1))) cap_new )
  **  (mpd_store_Z_compact UINT_MOD rp_addr_v (Zabs (x0)) (Zabs ((-1))) )
).

Definition mpz_set_si_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (((-(x_pre + 1 )) + 1 ) <= UINT_MAX)) (PreH2 : (((-(x_pre + 1 )) + 1 ) >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre < 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> ((-(x_pre + 1 )) + 1 ))
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ ((Zabs ((-1))) <= cap_new) ”
.

Definition mpz_set_si_return_wit_2_split_goal_2 := 
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (((-(x_pre + 1 )) + 1 ) <= UINT_MAX)) (PreH2 : (((-(x_pre + 1 )) + 1 ) >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre < 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> ((-(x_pre + 1 )) + 1 ))
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (same_sign x0 (-1) ) ”
.

Definition mpz_set_si_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (((-(x_pre + 1 )) + 1 ) <= UINT_MAX)) (PreH2 : (((-(x_pre + 1 )) + 1 ) >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre < 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> ((-(x_pre + 1 )) + 1 ))
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  (UIntArray.undef_seg rp_addr_v (Zabs ((-1))) cap_new )
  **  (mpd_store_Z_compact UINT_MOD rp_addr_v (Zabs (x0)) (Zabs ((-1))) )
.

Definition mpz_set_si_partial_solve_wit_1_pure := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (x_pre = x0)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (x_pre = x0) ” 
  &&  “ (0 <= x0) ”
.

Definition mpz_set_si_partial_solve_wit_1_aux := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (x_pre = x0)) ,
  (store_Z r_pre old )
|--
  “ (x_pre = x0) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x_pre >= 0) ” 
  &&  “ (x_pre = x0) ”
  &&  (store_Z r_pre old )
.

Definition mpz_set_si_partial_solve_wit_1 := mpz_set_si_partial_solve_wit_1_pure -> mpz_set_si_partial_solve_wit_1_aux.

Definition mpz_set_si_partial_solve_wit_2 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) ,
  (store_Z r_pre old )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (x_pre < 0) ” 
  &&  “ (x_pre = x0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_set_si_partial_solve_wit_3_pure := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) (PreH3 : (same_sign old size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (cap >= 0)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((Zabs ((-1))) <= (Z.max (1) (cap))) ”
.

Definition mpz_set_si_partial_solve_wit_3_aux := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (x_pre < 0)) (PreH2 : (x_pre = x0)) (PreH3 : (same_sign old size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (cap >= 0)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs ((-1))) <= (Z.max (1) (cap)))) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((Zabs ((-1))) <= (Z.max (1) (cap))) ” 
  &&  “ (x_pre < 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs ((-1))) <= (Z.max (1) (cap))) ”
  &&  (UIntArray.undef_full ptr cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_set_si_partial_solve_wit_3 := mpz_set_si_partial_solve_wit_3_pure -> mpz_set_si_partial_solve_wit_3_aux.

Definition mpz_set_si_partial_solve_wit_4 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre < 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (cap_new = (Z.max (1) (cap))) ” 
  &&  “ (x_pre < 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (cap_new >= 1) ” 
  &&  “ (cap_new <= INT_MAX) ”
  &&  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-1))
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_set_si_safety_wit_1 : mpz_set_si_safety_wit_1.
Axiom proof_of_mpz_set_si_safety_wit_2 : mpz_set_si_safety_wit_2.
Axiom proof_of_mpz_set_si_safety_wit_3 : mpz_set_si_safety_wit_3.
Axiom proof_of_mpz_set_si_safety_wit_4 : mpz_set_si_safety_wit_4.
Axiom proof_of_mpz_set_si_safety_wit_5 : mpz_set_si_safety_wit_5.
Axiom proof_of_mpz_set_si_safety_wit_6 : mpz_set_si_safety_wit_6.
Axiom proof_of_mpz_set_si_safety_wit_7 : mpz_set_si_safety_wit_7.
Axiom proof_of_mpz_set_si_safety_wit_8 : mpz_set_si_safety_wit_8.
Axiom proof_of_mpz_set_si_safety_wit_9 : mpz_set_si_safety_wit_9.
Axiom proof_of_mpz_set_si_safety_wit_10 : mpz_set_si_safety_wit_10.
Axiom proof_of_mpz_set_si_safety_wit_11 : mpz_set_si_safety_wit_11.
Axiom proof_of_mpz_set_si_entail_wit_1 : mpz_set_si_entail_wit_1.
Axiom proof_of_mpz_set_si_entail_wit_2 : mpz_set_si_entail_wit_2.
Axiom proof_of_mpz_set_si_return_wit_1 : mpz_set_si_return_wit_1.
Axiom proof_of_mpz_set_si_return_wit_2 : mpz_set_si_return_wit_2.
Axiom proof_of_mpz_set_si_partial_solve_wit_1_pure : mpz_set_si_partial_solve_wit_1_pure.
Axiom proof_of_mpz_set_si_partial_solve_wit_1 : mpz_set_si_partial_solve_wit_1.
Axiom proof_of_mpz_set_si_partial_solve_wit_2 : mpz_set_si_partial_solve_wit_2.
Axiom proof_of_mpz_set_si_partial_solve_wit_3_pure : mpz_set_si_partial_solve_wit_3_pure.
Axiom proof_of_mpz_set_si_partial_solve_wit_3 : mpz_set_si_partial_solve_wit_3.
Axiom proof_of_mpz_set_si_partial_solve_wit_4 : mpz_set_si_partial_solve_wit_4.

End VC_Correct.
