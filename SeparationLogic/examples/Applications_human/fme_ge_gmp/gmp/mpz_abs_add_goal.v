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

(*----- Function mpz_abs_add -----*)

Definition mpz_abs_add_safety_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 < retval)) (PreH2 : (retval = (Zabs (bsize)))) (PreH3 : (retval_2 = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 < retval)) (PreH2 : (retval = (Zabs (bsize)))) (PreH3 : (retval_2 = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
).

Definition mpz_abs_add_safety_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 < retval)) (PreH2 : (retval = (Zabs (bsize)))) (PreH3 : (retval_2 = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_safety_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 < retval)) (PreH2 : (retval = (Zabs (bsize)))) (PreH3 : (retval_2 = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition mpz_abs_add_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval_2)
  **  ((( &( "bn" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_abs_add_safety_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
).

Definition mpz_abs_add_safety_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_safety_wit_3_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition mpz_abs_add_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_abs_add_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (PreH1 : (r_pre = a_pre)) ,
  (store_Z a_pre za_r_eq_a )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (bptr: Z)  (rptr: Z)  (bcap: Z)  (rcap: Z)  (bsize: Z)  (rsize: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (cap_2 <= INT_MAX) ” 
  &&  “ (0 <= cap_2) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (size_2 <= INT_MAX) ” 
  &&  “ (INT_MIN < size_2) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
).

Definition mpz_abs_add_entail_wit_1_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (cap_2 <= INT_MAX) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_2 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (0 <= cap_2) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_3 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (cap <= INT_MAX) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_4 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (0 <= cap) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_5 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (size_2 <= INT_MAX) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_6 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (INT_MIN < size_2) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_7 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (size <= INT_MAX) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_8 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_add_entail_wit_1_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
.

Definition mpz_abs_add_entail_wit_2_rp_eq_ap := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval_3 (Zabs (rsize)) (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  EX (rcap_new: Z) ,
  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (retval < rcap_new) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
  **  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) retval )
  **  (UIntArray.undef_seg retval_3 retval rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  (UIntArray.undef_seg bptr retval_2 bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  “ (retval < z_callee__mp_alloc) ” 
  &&  “ (z_callee__mp_alloc <= INT_MAX) ” 
  &&  “ (0 <= z_callee__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= z_callee__mp_alloc) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
).

Definition mpz_abs_add_entail_wit_2_rp_eq_ap_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  “ (retval < z_callee__mp_alloc) ”
.

Definition mpz_abs_add_entail_wit_2_rp_eq_ap_split_goal_2 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  “ (z_callee__mp_alloc <= INT_MAX) ”
.

Definition mpz_abs_add_entail_wit_2_rp_eq_ap_split_goal_3 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  “ (0 <= z_callee__mp_alloc) ”
.

Definition mpz_abs_add_entail_wit_2_rp_eq_ap_split_goal_4 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  “ ((Zabs (rsize)) <= z_callee__mp_alloc) ”
.

Definition mpz_abs_add_entail_wit_2_rp_eq_ap_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval + 1 )) (1))) (rcap)))) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
.

Definition mpz_abs_add_entail_wit_3_rp_eq_bp := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval_2 + 1 )) (1))) (rcap)))) (PreH3 : (retval < retval_2)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval_3 (Zabs (rsize)) (Z.max ((Z.max ((retval_2 + 1 )) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  EX (rcap_new: Z) ,
  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (retval_2 < rcap_new) ” 
  &&  “ (retval <= rcap_new) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  (UIntArray.undef_seg bptr retval_2 bcap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
  **  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) retval )
  **  (UIntArray.undef_seg retval_3 retval retval_2 )
  **  (UIntArray.undef_seg retval_3 retval_2 rcap_new )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (z_callee__mp_alloc: Z) (retval_3: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (z_callee__mp_alloc >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (same_sign za_r_eq_a rsize )) (PreH5 : (z_callee__mp_alloc = (Z.max ((Z.max ((retval_2 + 1 )) (1))) (rcap)))) (PreH6 : (retval < retval_2)) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval_3 (Zabs (rsize)) (Z.max ((Z.max ((retval_2 + 1 )) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (rcap_new: Z) ,
  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (retval_2 < rcap_new) ” 
  &&  “ (retval <= rcap_new) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
  **  (mpd_store_Z_compact UINT_MOD retval_3 (Zabs (za_r_eq_a)) retval )
  **  (UIntArray.undef_seg retval_3 retval retval_2 )
  **  (UIntArray.undef_seg retval_3 retval_2 rcap_new )
).

Definition mpz_abs_add_entail_wit_4_rp_eq_bp := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (b: Z) (bn: Z) (an: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (zb_r_eq_a)) + (Zabs (za_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) an )) (PreH5 : (b = r_pre)) (PreH6 : (r_pre = a_pre)) (PreH7 : (bn < an)) (PreH8 : (an = (Zabs (bsize)))) (PreH9 : (bn = (Zabs (rsize)))) (PreH10 : (same_sign zb_r_eq_a bsize )) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : ((Zabs (bsize)) <= bcap)) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : (an < rcap_new)) (PreH17 : (bn <= rcap_new)) ,
  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (rcap_new >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (zb_r_eq_a)) + (Zabs (za_r_eq_a)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) an ) ” 
  &&  “ (b = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (bn < an) ” 
  &&  “ (an = (Zabs (bsize))) ” 
  &&  “ (bn = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (bn <= rcap_new) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
.

Definition mpz_abs_add_entail_wit_5_rp_eq_ap := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (a = r_pre)) (PreH6 : (r_pre = a_pre)) (PreH7 : (an >= bn)) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : (an < rcap_new)) ,
  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap_new >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an ) ” 
  &&  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_add_entail_wit_6_rp_eq_ap := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new_2: Z) (a: Z) (an: Z) (bn: Z) (val_r_out_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (bn <= INT_MAX)) (PreH7 : (an <= INT_MAX)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (rcap_new_2 >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (bn >= INT_MIN)) (PreH13 : (an >= INT_MIN)) (PreH14 : ((val_r_out_2 + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)) (PreH19 : (an >= bn)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new_2)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (0 <= rcap_new_2)) (PreH27 : (rcap_new_2 <= INT_MAX)) (PreH28 : (an < rcap_new_2)) ,
  (mpd_store_Z UINT_MOD rptr_new val_r_out_2 an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new_2)
  **  (UIntArray.undef_seg rptr_new an rcap_new_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (EX (val_r_out: Z)  (rcap_new: Z) ,
  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (retval = 0) ” 
  &&  “ (is_compact_Z UINT_MOD val_r_out an ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap ))
  ||
  (EX (val_r_out: Z)  (rcap_new: Z) ,
  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap ))
.

Definition mpz_abs_add_entail_wit_7_rp_eq_bp := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new_2: Z) (b: Z) (bn: Z) (an: Z) (val_r_out_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (an <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (rcap_new_2 >= INT_MIN)) (PreH9 : (rsize >= INT_MIN)) (PreH10 : (bcap >= INT_MIN)) (PreH11 : (bsize >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (bn >= INT_MIN)) (PreH14 : ((val_r_out_2 + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (zb_r_eq_a)) + (Zabs (za_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) an )) (PreH17 : (b = r_pre)) (PreH18 : (r_pre = a_pre)) (PreH19 : (bn < an)) (PreH20 : (an = (Zabs (bsize)))) (PreH21 : (bn = (Zabs (rsize)))) (PreH22 : (same_sign zb_r_eq_a bsize )) (PreH23 : (same_sign za_r_eq_a rsize )) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : ((Zabs (rsize)) <= rcap_new_2)) (PreH26 : (0 <= rcap_new_2)) (PreH27 : (rcap_new_2 <= INT_MAX)) (PreH28 : (an < rcap_new_2)) (PreH29 : (bn <= rcap_new_2)) ,
  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out_2 an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new_2 )
|--
  (EX (val_r_out: Z)  (rcap_new: Z) ,
  “ (b = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (bn < an) ” 
  &&  “ (an = (Zabs (bsize))) ” 
  &&  “ (bn = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (retval = 0) ” 
  &&  “ (is_compact_Z UINT_MOD val_r_out an ) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new ))
  ||
  (EX (val_r_out: Z)  (rcap_new: Z) ,
  “ (b = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (bn < an) ” 
  &&  “ (an = (Zabs (bsize))) ” 
  &&  “ (bn = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) ) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new ))
.

Definition mpz_abs_add_return_wit_1_rp_eq_bp := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (b = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (bn < an)) (PreH4 : (an = (Zabs (bsize)))) (PreH5 : (bn = (Zabs (rsize)))) (PreH6 : (same_sign zb_r_eq_a bsize )) (PreH7 : (same_sign za_r_eq_a rsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Zabs (rsize)) <= rcap_new)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (bn <= rcap_new)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= 1)) (PreH16 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH17 : (cy = 0)) (PreH18 : (is_compact_Z UINT_MOD val_r_out an )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (b = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (bn < an)) (PreH9 : (an = (Zabs (bsize)))) (PreH10 : (bn = (Zabs (rsize)))) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : ((Zabs (rsize)) <= rcap_new)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (bn <= rcap_new)) (PreH19 : (0 <= cy)) (PreH20 : (cy <= 1)) (PreH21 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH22 : (cy = 0)) (PreH23 : (is_compact_Z UINT_MOD val_r_out an )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
).

Definition mpz_abs_add_return_wit_1_rp_eq_bp_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (b = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (bn < an)) (PreH9 : (an = (Zabs (bsize)))) (PreH10 : (bn = (Zabs (rsize)))) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : ((Zabs (rsize)) <= rcap_new)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (bn <= rcap_new)) (PreH19 : (0 <= cy)) (PreH20 : (cy <= 1)) (PreH21 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH22 : (cy = 0)) (PreH23 : (is_compact_Z UINT_MOD val_r_out an )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
.

Definition mpz_abs_add_return_wit_2_rp_eq_bp := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (b = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (bn < an)) (PreH4 : (an = (Zabs (bsize)))) (PreH5 : (bn = (Zabs (rsize)))) (PreH6 : (same_sign zb_r_eq_a bsize )) (PreH7 : (same_sign za_r_eq_a rsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Zabs (rsize)) <= rcap_new)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (bn <= rcap_new)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= 1)) (PreH16 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH17 : (cy = 1)) (PreH18 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (b = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (bn < an)) (PreH9 : (an = (Zabs (bsize)))) (PreH10 : (bn = (Zabs (rsize)))) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : ((Zabs (rsize)) <= rcap_new)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (bn <= rcap_new)) (PreH19 : (0 <= cy)) (PreH20 : (cy <= 1)) (PreH21 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH22 : (cy = 1)) (PreH23 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
).

Definition mpz_abs_add_return_wit_2_rp_eq_bp_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (b = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (bn < an)) (PreH9 : (an = (Zabs (bsize)))) (PreH10 : (bn = (Zabs (rsize)))) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : ((Zabs (rsize)) <= rcap_new)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (bn <= rcap_new)) (PreH19 : (0 <= cy)) (PreH20 : (cy <= 1)) (PreH21 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH22 : (cy = 1)) (PreH23 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
.

Definition mpz_abs_add_return_wit_3_rp_eq_ap := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (0 <= cy)) (PreH14 : (cy <= 1)) (PreH15 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH16 : (cy = 0)) (PreH17 : (is_compact_Z UINT_MOD val_r_out an )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (a = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (an >= bn)) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (0 <= cy)) (PreH19 : (cy <= 1)) (PreH20 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH21 : (cy = 0)) (PreH22 : (is_compact_Z UINT_MOD val_r_out an )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
).

Definition mpz_abs_add_return_wit_3_rp_eq_ap_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (a = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (an >= bn)) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (0 <= cy)) (PreH19 : (cy <= 1)) (PreH20 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH21 : (cy = 0)) (PreH22 : (is_compact_Z UINT_MOD val_r_out an )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
.

Definition mpz_abs_add_return_wit_4_rp_eq_ap := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (0 <= cy)) (PreH14 : (cy <= 1)) (PreH15 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH16 : (cy = 1)) (PreH17 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (a = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (an >= bn)) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (0 <= cy)) (PreH19 : (cy <= 1)) (PreH20 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH21 : (cy = 1)) (PreH22 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
).

Definition mpz_abs_add_return_wit_4_rp_eq_ap_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (cy <= UINT_MAX)) (PreH2 : (cy >= 0)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (rcap_new >= INT_MIN)) (PreH5 : (rsize >= INT_MIN)) (PreH6 : (a = r_pre)) (PreH7 : (r_pre = a_pre)) (PreH8 : (an >= bn)) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (0 <= rcap_new)) (PreH16 : (rcap_new <= INT_MAX)) (PreH17 : (an < rcap_new)) (PreH18 : (0 <= cy)) (PreH19 : (cy <= 1)) (PreH20 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH21 : (cy = 1)) (PreH22 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  (((rptr_new + (an * sizeof(UINT)))) # UInt  |-> cy)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + cy )) (32)) )
.

Definition mpz_abs_add_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (INT_MIN < rsize)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (INT_MIN < bsize)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (0 <= rcap)) (PreH7 : (rcap <= INT_MAX)) (PreH8 : (0 <= bcap)) (PreH9 : (bcap <= INT_MAX)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : ((Zabs (bsize)) <= bcap)) (PreH13 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (INT_MIN < rsize)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (INT_MIN < bsize)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (0 <= rcap)) (PreH7 : (rcap <= INT_MAX)) (PreH8 : (0 <= bcap)) (PreH9 : (bcap <= INT_MAX)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : ((Zabs (bsize)) <= bcap)) (PreH13 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_add_partial_solve_wit_1 := mpz_abs_add_partial_solve_wit_1_pure -> mpz_abs_add_partial_solve_wit_1_aux.

Definition mpz_abs_add_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (PreH1 : (retval = (Zabs (rsize)))) (PreH2 : (r_pre = a_pre)) (PreH3 : (INT_MIN < rsize)) (PreH4 : (rsize <= INT_MAX)) (PreH5 : (INT_MIN < bsize)) (PreH6 : (bsize <= INT_MAX)) (PreH7 : (0 <= rcap)) (PreH8 : (rcap <= INT_MAX)) (PreH9 : (0 <= bcap)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (PreH1 : (retval = (Zabs (rsize)))) (PreH2 : (r_pre = a_pre)) (PreH3 : (INT_MIN < rsize)) (PreH4 : (rsize <= INT_MAX)) (PreH5 : (INT_MIN < bsize)) (PreH6 : (bsize <= INT_MAX)) (PreH7 : (0 <= rcap)) (PreH8 : (rcap <= INT_MAX)) (PreH9 : (0 <= bcap)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_add_partial_solve_wit_2 := mpz_abs_add_partial_solve_wit_2_pure -> mpz_abs_add_partial_solve_wit_2_aux.

Definition mpz_abs_add_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_add_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_add_partial_solve_wit_5_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 < retval)) (PreH2 : (retval = (Zabs (bsize)))) (PreH3 : (retval_2 = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((retval + 1 ) >= 1) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (((Zabs (bsize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (bsize)) + 1 ) >= 1) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval_2 < retval)) (PreH10 : (retval = (Zabs (bsize)))) (PreH11 : (retval_2 = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (((Zabs (bsize)) + 1 ) >= 1) ” 
  &&  “ (((Zabs (bsize)) + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) >= 1) ”
).

Definition mpz_abs_add_partial_solve_wit_5_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval_2 < retval)) (PreH10 : (retval = (Zabs (bsize)))) (PreH11 : (retval_2 = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (((Zabs (bsize)) + 1 ) >= 1) ”
.

Definition mpz_abs_add_partial_solve_wit_5_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval_2 < retval)) (PreH10 : (retval = (Zabs (bsize)))) (PreH11 : (retval_2 = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (((Zabs (bsize)) + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_5_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval_2 < retval)) (PreH10 : (retval = (Zabs (bsize)))) (PreH11 : (retval_2 = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_5_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval_2 < retval)) (PreH10 : (retval = (Zabs (bsize)))) (PreH11 : (retval_2 = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "b" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) >= 1) ”
.

Definition mpz_abs_add_partial_solve_wit_5_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 < retval)) (PreH2 : (retval = (Zabs (bsize)))) (PreH3 : (retval_2 = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((retval + 1 ) >= 1) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (((Zabs (bsize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (bsize)) + 1 ) >= 1) ” 
  &&  “ (retval_2 < retval) ” 
  &&  “ (retval = (Zabs (bsize))) ” 
  &&  “ (retval_2 = (Zabs (rsize))) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_add_partial_solve_wit_5 := mpz_abs_add_partial_solve_wit_5_pure -> mpz_abs_add_partial_solve_wit_5_aux.

Definition mpz_abs_add_partial_solve_wit_6_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((retval + 1 ) >= 1) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (((Zabs (rsize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (rsize)) + 1 ) >= 1) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval >= retval_2)) (PreH10 : (retval_2 = (Zabs (bsize)))) (PreH11 : (retval = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (((Zabs (rsize)) + 1 ) >= 1) ” 
  &&  “ (((Zabs (rsize)) + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) >= 1) ”
).

Definition mpz_abs_add_partial_solve_wit_6_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval >= retval_2)) (PreH10 : (retval_2 = (Zabs (bsize)))) (PreH11 : (retval = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (((Zabs (rsize)) + 1 ) >= 1) ”
.

Definition mpz_abs_add_partial_solve_wit_6_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval >= retval_2)) (PreH10 : (retval_2 = (Zabs (bsize)))) (PreH11 : (retval = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (((Zabs (rsize)) + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_6_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval >= retval_2)) (PreH10 : (retval_2 = (Zabs (bsize)))) (PreH11 : (retval = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_6_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval >= retval_2)) (PreH10 : (retval_2 = (Zabs (bsize)))) (PreH11 : (retval = (Zabs (rsize)))) (PreH12 : (r_pre = a_pre)) (PreH13 : (INT_MIN < rsize)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (INT_MIN < bsize)) (PreH16 : (bsize <= INT_MAX)) (PreH17 : (0 <= rcap)) (PreH18 : (rcap <= INT_MAX)) (PreH19 : (0 <= bcap)) (PreH20 : (bcap <= INT_MAX)) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : ((Zabs (bsize)) <= bcap)) (PreH24 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ ((retval + 1 ) >= 1) ”
.

Definition mpz_abs_add_partial_solve_wit_6_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (bsize)))) (PreH3 : (retval = (Zabs (rsize)))) (PreH4 : (r_pre = a_pre)) (PreH5 : (INT_MIN < rsize)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (INT_MIN < bsize)) (PreH8 : (bsize <= INT_MAX)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : (0 <= bcap)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((retval + 1 ) >= 1) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (((Zabs (rsize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (rsize)) + 1 ) >= 1) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (INT_MIN < rsize) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (INT_MIN < bsize) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bcap) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_add_partial_solve_wit_6 := mpz_abs_add_partial_solve_wit_6_pure -> mpz_abs_add_partial_solve_wit_6_aux.

Definition mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (b: Z) (bn: Z) (an: Z) (PreH1 : (b = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (bn < an)) (PreH4 : (an = (Zabs (bsize)))) (PreH5 : (bn = (Zabs (rsize)))) (PreH6 : (same_sign zb_r_eq_a bsize )) (PreH7 : (same_sign za_r_eq_a rsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Zabs (rsize)) <= rcap_new)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (bn <= rcap_new)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) bn )
  **  (UIntArray.undef_seg rptr_new bn an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (an >= bn) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an >= 0) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (b: Z) (bn: Z) (an: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (bcap <= INT_MAX)) (PreH3 : (bsize <= INT_MAX)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn <= INT_MAX)) (PreH6 : (rcap_new >= INT_MIN)) (PreH7 : (rsize >= INT_MIN)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (an >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (b = r_pre)) (PreH13 : (r_pre = a_pre)) (PreH14 : (bn < an)) (PreH15 : (an = (Zabs (bsize)))) (PreH16 : (bn = (Zabs (rsize)))) (PreH17 : (same_sign zb_r_eq_a bsize )) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : ((Zabs (rsize)) <= rcap_new)) (PreH21 : (0 <= rcap_new)) (PreH22 : (rcap_new <= INT_MAX)) (PreH23 : (an < rcap_new)) (PreH24 : (bn <= rcap_new)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) bn )
  **  (UIntArray.undef_seg rptr_new bn an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (an >= 0) ” 
  &&  “ (bn >= 0) ”
).

Definition mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (b: Z) (bn: Z) (an: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (bcap <= INT_MAX)) (PreH3 : (bsize <= INT_MAX)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn <= INT_MAX)) (PreH6 : (rcap_new >= INT_MIN)) (PreH7 : (rsize >= INT_MIN)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (an >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (b = r_pre)) (PreH13 : (r_pre = a_pre)) (PreH14 : (bn < an)) (PreH15 : (an = (Zabs (bsize)))) (PreH16 : (bn = (Zabs (rsize)))) (PreH17 : (same_sign zb_r_eq_a bsize )) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : ((Zabs (rsize)) <= rcap_new)) (PreH21 : (0 <= rcap_new)) (PreH22 : (rcap_new <= INT_MAX)) (PreH23 : (an < rcap_new)) (PreH24 : (bn <= rcap_new)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) bn )
  **  (UIntArray.undef_seg rptr_new bn an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (an >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (b: Z) (bn: Z) (an: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (bcap <= INT_MAX)) (PreH3 : (bsize <= INT_MAX)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn <= INT_MAX)) (PreH6 : (rcap_new >= INT_MIN)) (PreH7 : (rsize >= INT_MIN)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (an >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (b = r_pre)) (PreH13 : (r_pre = a_pre)) (PreH14 : (bn < an)) (PreH15 : (an = (Zabs (bsize)))) (PreH16 : (bn = (Zabs (rsize)))) (PreH17 : (same_sign zb_r_eq_a bsize )) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : ((Zabs (rsize)) <= rcap_new)) (PreH21 : (0 <= rcap_new)) (PreH22 : (rcap_new <= INT_MAX)) (PreH23 : (an < rcap_new)) (PreH24 : (bn <= rcap_new)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> b_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) bn )
  **  (UIntArray.undef_seg rptr_new bn an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (bn >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_7_rp_eq_bp_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (b: Z) (bn: Z) (an: Z) (PreH1 : (b = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (bn < an)) (PreH4 : (an = (Zabs (bsize)))) (PreH5 : (bn = (Zabs (rsize)))) (PreH6 : (same_sign zb_r_eq_a bsize )) (PreH7 : (same_sign za_r_eq_a rsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Zabs (rsize)) <= rcap_new)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (bn <= rcap_new)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) bn )
  **  (UIntArray.undef_seg rptr_new bn an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (an >= bn) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) an ) ” 
  &&  “ (b = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (bn < an) ” 
  &&  “ (an = (Zabs (bsize))) ” 
  &&  “ (bn = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (bn <= rcap_new) ”
  &&  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (mpd_store_Z UINT_MOD rptr_new (Zabs (za_r_eq_a)) bn )
  **  (UIntArray.undef_seg rptr_new bn an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
.

Definition mpz_abs_add_partial_solve_wit_7_rp_eq_bp := mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure -> mpz_abs_add_partial_solve_wit_7_rp_eq_bp_aux.

Definition mpz_abs_add_partial_solve_wit_8_rp_eq_ap := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ”
  &&  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (an >= bn) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an >= 0) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (bcap >= INT_MIN)) (PreH7 : (bsize >= INT_MIN)) (PreH8 : (rcap_new >= INT_MIN)) (PreH9 : (rsize >= INT_MIN)) (PreH10 : (bn >= INT_MIN)) (PreH11 : (an >= INT_MIN)) (PreH12 : (a = r_pre)) (PreH13 : (r_pre = a_pre)) (PreH14 : (an >= bn)) (PreH15 : (an = (Zabs (rsize)))) (PreH16 : (bn = (Zabs (bsize)))) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : (same_sign zb_r_eq_a bsize )) (PreH19 : ((Zabs (rsize)) <= rcap_new)) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (0 <= rcap_new)) (PreH22 : (rcap_new <= INT_MAX)) (PreH23 : (an < rcap_new)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (an >= 0) ” 
  &&  “ (bn >= 0) ”
).

Definition mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (bcap >= INT_MIN)) (PreH7 : (bsize >= INT_MIN)) (PreH8 : (rcap_new >= INT_MIN)) (PreH9 : (rsize >= INT_MIN)) (PreH10 : (bn >= INT_MIN)) (PreH11 : (an >= INT_MIN)) (PreH12 : (a = r_pre)) (PreH13 : (r_pre = a_pre)) (PreH14 : (an >= bn)) (PreH15 : (an = (Zabs (rsize)))) (PreH16 : (bn = (Zabs (bsize)))) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : (same_sign zb_r_eq_a bsize )) (PreH19 : ((Zabs (rsize)) <= rcap_new)) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (0 <= rcap_new)) (PreH22 : (rcap_new <= INT_MAX)) (PreH23 : (an < rcap_new)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (an >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (bcap >= INT_MIN)) (PreH7 : (bsize >= INT_MIN)) (PreH8 : (rcap_new >= INT_MIN)) (PreH9 : (rsize >= INT_MIN)) (PreH10 : (bn >= INT_MIN)) (PreH11 : (an >= INT_MIN)) (PreH12 : (a = r_pre)) (PreH13 : (r_pre = a_pre)) (PreH14 : (an >= bn)) (PreH15 : (an = (Zabs (rsize)))) (PreH16 : (bn = (Zabs (bsize)))) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : (same_sign zb_r_eq_a bsize )) (PreH19 : ((Zabs (rsize)) <= rcap_new)) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (0 <= rcap_new)) (PreH22 : (rcap_new <= INT_MAX)) (PreH23 : (an < rcap_new)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (bn >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_9_rp_eq_ap_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (an >= bn) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an ) ” 
  &&  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ”
  &&  (mpd_store_Z UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_add_partial_solve_wit_9_rp_eq_ap := mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure -> mpz_abs_add_partial_solve_wit_9_rp_eq_ap_aux.

Definition mpz_abs_add_partial_solve_wit_10_rp_eq_bp := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (b = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (bn < an)) (PreH4 : (an = (Zabs (bsize)))) (PreH5 : (bn = (Zabs (rsize)))) (PreH6 : (same_sign zb_r_eq_a bsize )) (PreH7 : (same_sign za_r_eq_a rsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Zabs (rsize)) <= rcap_new)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (bn <= rcap_new)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= 1)) (PreH16 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH17 : (cy = 0)) (PreH18 : (is_compact_Z UINT_MOD val_r_out an )) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (b = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (bn < an) ” 
  &&  “ (an = (Zabs (bsize))) ” 
  &&  “ (bn = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 1) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (cy = 0) ” 
  &&  “ (is_compact_Z UINT_MOD val_r_out an ) ”
  &&  (((rptr_new + (an * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
.

Definition mpz_abs_add_partial_solve_wit_11_rp_eq_bp := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (b: Z) (bn: Z) (an: Z) (cy: Z) (PreH1 : (b = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (bn < an)) (PreH4 : (an = (Zabs (bsize)))) (PreH5 : (bn = (Zabs (rsize)))) (PreH6 : (same_sign zb_r_eq_a bsize )) (PreH7 : (same_sign za_r_eq_a rsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Zabs (rsize)) <= rcap_new)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (bn <= rcap_new)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= 1)) (PreH16 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH17 : (cy = 1)) (PreH18 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  “ (b = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (bn < an) ” 
  &&  “ (an = (Zabs (bsize))) ” 
  &&  “ (bn = (Zabs (rsize))) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 1) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (cy = 1) ” 
  &&  “ (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) ) ”
  &&  (((rptr_new + (an * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) an )
  **  (UIntArray.undef_seg bptr an bcap )
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
.

Definition mpz_abs_add_partial_solve_wit_12_rp_eq_ap := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (0 <= cy)) (PreH14 : (cy <= 1)) (PreH15 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH16 : (cy = 0)) (PreH17 : (is_compact_Z UINT_MOD val_r_out an )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 1) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (cy = 0) ” 
  &&  “ (is_compact_Z UINT_MOD val_r_out an ) ”
  &&  (((rptr_new + (an * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_add_partial_solve_wit_13_rp_eq_ap := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (val_r_out: Z) (a: Z) (an: Z) (bn: Z) (cy: Z) (PreH1 : (a = r_pre)) (PreH2 : (r_pre = a_pre)) (PreH3 : (an >= bn)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : ((Zabs (bsize)) <= bcap)) (PreH10 : (0 <= rcap_new)) (PreH11 : (rcap_new <= INT_MAX)) (PreH12 : (an < rcap_new)) (PreH13 : (0 <= cy)) (PreH14 : (cy <= 1)) (PreH15 : ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ))) (PreH16 : (cy = 1)) (PreH17 : (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ (an < rcap_new) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 1) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (cy = 1) ” 
  &&  “ (is_compact_Z UINT_MOD (val_r_out + (Z.pow (UINT_MOD) (an)) ) (an + 1 ) ) ”
  &&  (((rptr_new + (an * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rptr_new (an + 1 ) rcap_new )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_abs_add_safety_wit_1 : mpz_abs_add_safety_wit_1.
Axiom proof_of_mpz_abs_add_safety_wit_2 : mpz_abs_add_safety_wit_2.
Axiom proof_of_mpz_abs_add_safety_wit_3 : mpz_abs_add_safety_wit_3.
Axiom proof_of_mpz_abs_add_safety_wit_4 : mpz_abs_add_safety_wit_4.
Axiom proof_of_mpz_abs_add_entail_wit_1 : mpz_abs_add_entail_wit_1.
Axiom proof_of_mpz_abs_add_entail_wit_2_rp_eq_ap : mpz_abs_add_entail_wit_2_rp_eq_ap.
Axiom proof_of_mpz_abs_add_entail_wit_3_rp_eq_bp : mpz_abs_add_entail_wit_3_rp_eq_bp.
Axiom proof_of_mpz_abs_add_entail_wit_4_rp_eq_bp : mpz_abs_add_entail_wit_4_rp_eq_bp.
Axiom proof_of_mpz_abs_add_entail_wit_5_rp_eq_ap : mpz_abs_add_entail_wit_5_rp_eq_ap.
Axiom proof_of_mpz_abs_add_entail_wit_6_rp_eq_ap : mpz_abs_add_entail_wit_6_rp_eq_ap.
Axiom proof_of_mpz_abs_add_entail_wit_7_rp_eq_bp : mpz_abs_add_entail_wit_7_rp_eq_bp.
Axiom proof_of_mpz_abs_add_return_wit_1_rp_eq_bp : mpz_abs_add_return_wit_1_rp_eq_bp.
Axiom proof_of_mpz_abs_add_return_wit_2_rp_eq_bp : mpz_abs_add_return_wit_2_rp_eq_bp.
Axiom proof_of_mpz_abs_add_return_wit_3_rp_eq_ap : mpz_abs_add_return_wit_3_rp_eq_ap.
Axiom proof_of_mpz_abs_add_return_wit_4_rp_eq_ap : mpz_abs_add_return_wit_4_rp_eq_ap.
Axiom proof_of_mpz_abs_add_partial_solve_wit_1_pure : mpz_abs_add_partial_solve_wit_1_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_1 : mpz_abs_add_partial_solve_wit_1.
Axiom proof_of_mpz_abs_add_partial_solve_wit_2_pure : mpz_abs_add_partial_solve_wit_2_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_2 : mpz_abs_add_partial_solve_wit_2.
Axiom proof_of_mpz_abs_add_partial_solve_wit_3 : mpz_abs_add_partial_solve_wit_3.
Axiom proof_of_mpz_abs_add_partial_solve_wit_4 : mpz_abs_add_partial_solve_wit_4.
Axiom proof_of_mpz_abs_add_partial_solve_wit_5_pure : mpz_abs_add_partial_solve_wit_5_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_5 : mpz_abs_add_partial_solve_wit_5.
Axiom proof_of_mpz_abs_add_partial_solve_wit_6_pure : mpz_abs_add_partial_solve_wit_6_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_6 : mpz_abs_add_partial_solve_wit_6.
Axiom proof_of_mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure : mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_7_rp_eq_bp : mpz_abs_add_partial_solve_wit_7_rp_eq_bp.
Axiom proof_of_mpz_abs_add_partial_solve_wit_8_rp_eq_ap : mpz_abs_add_partial_solve_wit_8_rp_eq_ap.
Axiom proof_of_mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure : mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_9_rp_eq_ap : mpz_abs_add_partial_solve_wit_9_rp_eq_ap.
Axiom proof_of_mpz_abs_add_partial_solve_wit_10_rp_eq_bp : mpz_abs_add_partial_solve_wit_10_rp_eq_bp.
Axiom proof_of_mpz_abs_add_partial_solve_wit_11_rp_eq_bp : mpz_abs_add_partial_solve_wit_11_rp_eq_bp.
Axiom proof_of_mpz_abs_add_partial_solve_wit_12_rp_eq_ap : mpz_abs_add_partial_solve_wit_12_rp_eq_ap.
Axiom proof_of_mpz_abs_add_partial_solve_wit_13_rp_eq_ap : mpz_abs_add_partial_solve_wit_13_rp_eq_ap.

End VC_Correct.
