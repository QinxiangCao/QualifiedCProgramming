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

(*----- Function mpz_abs_sub -----*)

Definition mpz_abs_sub_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH2 : (retval_3 = (-1))) (PreH3 : (retval_2 = (Zabs (bsize)))) (PreH4 : (retval = (Zabs (rsize)))) (PreH5 : (r_pre = a_pre)) (PreH6 : (INT_MIN < rsize)) (PreH7 : (rsize <= INT_MAX)) (PreH8 : (INT_MIN < bsize)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (0 <= rcap)) (PreH11 : (rcap <= INT_MAX)) (PreH12 : (0 <= bcap)) (PreH13 : (bcap <= INT_MAX)) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (same_sign za_r_eq_a rsize )) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_2 = (Zabs (bsize)))) (PreH4 : (retval = (Zabs (rsize)))) (PreH5 : (r_pre = a_pre)) (PreH6 : (INT_MIN < rsize)) (PreH7 : (rsize <= INT_MAX)) (PreH8 : (INT_MIN < bsize)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (0 <= rcap)) (PreH11 : (rcap <= INT_MAX)) (PreH12 : (0 <= bcap)) (PreH13 : (bcap <= INT_MAX)) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (same_sign za_r_eq_a rsize )) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = (Zabs (bsize)))) (PreH4 : (retval = (Zabs (rsize)))) (PreH5 : (r_pre = a_pre)) (PreH6 : (INT_MIN < rsize)) (PreH7 : (rsize <= INT_MAX)) (PreH8 : (INT_MIN < bsize)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (0 <= rcap)) (PreH11 : (rcap <= INT_MAX)) (PreH12 : (0 <= bcap)) (PreH13 : (bcap <= INT_MAX)) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (same_sign za_r_eq_a rsize )) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH6 : (cmp < 0)) (PreH7 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH8 : (cmp = (-1))) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (bn <= rcap_new)) (PreH18 : (a = r_pre)) (PreH19 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval bn )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_abs_sub_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_entail_wit_1 := 
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
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  TT && emp 
|--
  “ (cap_2 <= INT_MAX) ” 
  &&  “ (0 <= cap_2) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (size_2 <= INT_MAX) ” 
  &&  “ (INT_MIN < size_2) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_1_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (cap_2 <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_2 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (0 <= cap_2)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_3 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (cap <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_4 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (0 <= cap)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_5 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (size_2 <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_6 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (INT_MIN < size_2)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_7 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (size <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_split_goal_8 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  (INT_MIN < size)
.

Definition mpz_abs_sub_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (retval_3 > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  (UIntArray.undef_seg bptr retval_2 bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (bsize)))) (PreH7 : (retval = (Zabs (rsize)))) (PreH8 : (r_pre = a_pre)) (PreH9 : (INT_MIN < rsize)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (INT_MIN < bsize)) (PreH12 : (bsize <= INT_MAX)) (PreH13 : (0 <= rcap)) (PreH14 : (rcap <= INT_MAX)) (PreH15 : (0 <= bcap)) (PreH16 : (bcap <= INT_MAX)) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
|--
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
).

Definition mpz_abs_sub_entail_wit_2_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (bsize)))) (PreH7 : (retval = (Zabs (rsize)))) (PreH8 : (r_pre = a_pre)) (PreH9 : (INT_MIN < rsize)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (INT_MIN < bsize)) (PreH12 : (bsize <= INT_MAX)) (PreH13 : (0 <= rcap)) (PreH14 : (rcap <= INT_MAX)) (PreH15 : (0 <= bcap)) (PreH16 : (bcap <= INT_MAX)) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
|--
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
.

Definition mpz_abs_sub_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = 1)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (1 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)) ,
  TT && emp 
|--
  “ (1 <= an) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_3_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)) ,
  (1 <= an)
.

Definition mpz_abs_sub_entail_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (1 <= an)) (PreH2 : (an <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (bn <= INT_MAX)) (PreH7 : (cmp <= INT_MAX)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (bn >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)) ,
  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (1 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (an >= INT_MIN)) (PreH2 : (1 <= an)) (PreH3 : (an <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (bn >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp > 0)) (PreH16 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = 1)) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)) ,
  TT && emp 
|--
  “ (0 <= bn) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_4_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (an >= INT_MIN)) (PreH2 : (1 <= an)) (PreH3 : (an <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (bn >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp > 0)) (PreH16 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = 1)) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)) ,
  (0 <= bn)
.

Definition mpz_abs_sub_entail_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= bn)) (PreH2 : (bn <= INT_MAX)) (PreH3 : (an >= INT_MIN)) (PreH4 : (1 <= an)) (PreH5 : (an <= INT_MAX)) (PreH6 : (bcap <= INT_MAX)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (bn <= INT_MAX)) (PreH10 : (cmp <= INT_MAX)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (rcap >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (cmp >= INT_MIN)) (PreH17 : (cmp > 0)) (PreH18 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = 1)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap)) (PreH25 : (0 <= rcap)) (PreH26 : (rcap <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (r_pre = a_pre)) ,
  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (1 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_entail_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH3 : (0 <= rcap)) (PreH4 : (rcap <= INT_MAX)) (PreH5 : (0 <= bn)) (PreH6 : (bn <= INT_MAX)) (PreH7 : (an >= INT_MIN)) (PreH8 : (1 <= an)) (PreH9 : (an <= INT_MAX)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (rsize <= INT_MAX)) (PreH13 : (bn <= INT_MAX)) (PreH14 : (cmp <= INT_MAX)) (PreH15 : (bcap >= INT_MIN)) (PreH16 : (bsize >= INT_MIN)) (PreH17 : (rcap >= INT_MIN)) (PreH18 : (rsize >= INT_MIN)) (PreH19 : (bn >= INT_MIN)) (PreH20 : (cmp >= INT_MIN)) (PreH21 : (cmp > 0)) (PreH22 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH23 : (cmp = 1)) (PreH24 : (an = (Zabs (rsize)))) (PreH25 : (bn = (Zabs (bsize)))) (PreH26 : (same_sign za_r_eq_a rsize )) (PreH27 : (same_sign zb_r_eq_a bsize )) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (0 <= rcap)) (PreH30 : (rcap <= INT_MAX)) (PreH31 : ((Zabs (bsize)) <= bcap)) (PreH32 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max ((Z.max (an) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  EX (rcap_new: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (an <= rcap_new) ” 
  &&  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg retval an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (z_callee__mp_alloc >= INT_MIN)) (PreH3 : (same_sign za_r_eq_a rsize )) (PreH4 : (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH5 : (0 <= rcap)) (PreH6 : (rcap <= INT_MAX)) (PreH7 : (0 <= bn)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (an >= INT_MIN)) (PreH10 : (1 <= an)) (PreH11 : (an <= INT_MAX)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (bn <= INT_MAX)) (PreH16 : (cmp <= INT_MAX)) (PreH17 : (bcap >= INT_MIN)) (PreH18 : (bsize >= INT_MIN)) (PreH19 : (rcap >= INT_MIN)) (PreH20 : (rsize >= INT_MIN)) (PreH21 : (bn >= INT_MIN)) (PreH22 : (cmp >= INT_MIN)) (PreH23 : (cmp > 0)) (PreH24 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH25 : (cmp = 1)) (PreH26 : (an = (Zabs (rsize)))) (PreH27 : (bn = (Zabs (bsize)))) (PreH28 : (same_sign za_r_eq_a rsize )) (PreH29 : (same_sign zb_r_eq_a bsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (0 <= rcap)) (PreH32 : (rcap <= INT_MAX)) (PreH33 : ((Zabs (bsize)) <= bcap)) (PreH34 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max ((Z.max (an) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  EX (rcap_new: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (an <= rcap_new) ” 
  &&  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg retval an rcap_new )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
).

Definition mpz_abs_sub_entail_wit_7 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (retval_3 < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval = (Zabs (rsize))) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  (UIntArray.undef_seg bptr retval_2 bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
|--
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
).

Definition mpz_abs_sub_entail_wit_7_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
|--
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
.

Definition mpz_abs_sub_entail_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (cmp < 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = (-1))) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (1 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)) ,
  TT && emp 
|--
  “ (1 <= bn) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_8_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)) ,
  (1 <= bn)
.

Definition mpz_abs_sub_entail_wit_9 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (1 <= bn)) (PreH2 : (bn <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (an <= INT_MAX)) (PreH7 : (cmp <= INT_MAX)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)) ,
  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (1 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bn >= INT_MIN)) (PreH2 : (1 <= bn)) (PreH3 : (bn <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (an <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (an >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp < 0)) (PreH16 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = (-1))) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)) ,
  TT && emp 
|--
  “ (0 <= an) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_9_split_goal_1 := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bn >= INT_MIN)) (PreH2 : (1 <= bn)) (PreH3 : (bn <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (an <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (an >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp < 0)) (PreH16 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = (-1))) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)) ,
  (0 <= an)
.

Definition mpz_abs_sub_entail_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= an)) (PreH2 : (an <= INT_MAX)) (PreH3 : (bn >= INT_MIN)) (PreH4 : (1 <= bn)) (PreH5 : (bn <= INT_MAX)) (PreH6 : (bcap <= INT_MAX)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (an <= INT_MAX)) (PreH10 : (cmp <= INT_MAX)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (rcap >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (an >= INT_MIN)) (PreH16 : (cmp >= INT_MIN)) (PreH17 : (cmp < 0)) (PreH18 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = (-1))) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap)) (PreH25 : (0 <= rcap)) (PreH26 : (rcap <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (r_pre = a_pre)) ,
  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (1 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_entail_wit_11 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH3 : (0 <= rcap)) (PreH4 : (rcap <= INT_MAX)) (PreH5 : (0 <= an)) (PreH6 : (an <= INT_MAX)) (PreH7 : (bn >= INT_MIN)) (PreH8 : (1 <= bn)) (PreH9 : (bn <= INT_MAX)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (rsize <= INT_MAX)) (PreH13 : (an <= INT_MAX)) (PreH14 : (cmp <= INT_MAX)) (PreH15 : (bcap >= INT_MIN)) (PreH16 : (bsize >= INT_MIN)) (PreH17 : (rcap >= INT_MIN)) (PreH18 : (rsize >= INT_MIN)) (PreH19 : (an >= INT_MIN)) (PreH20 : (cmp >= INT_MIN)) (PreH21 : (cmp < 0)) (PreH22 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH23 : (cmp = (-1))) (PreH24 : (an = (Zabs (rsize)))) (PreH25 : (bn = (Zabs (bsize)))) (PreH26 : (same_sign za_r_eq_a rsize )) (PreH27 : (same_sign zb_r_eq_a bsize )) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (0 <= rcap)) (PreH30 : (rcap <= INT_MAX)) (PreH31 : ((Zabs (bsize)) <= bcap)) (PreH32 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max ((Z.max (bn) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  EX (rcap_new: Z) ,
  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg retval an bn )
  **  (UIntArray.undef_seg retval bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (z_callee__mp_alloc >= INT_MIN)) (PreH3 : (same_sign za_r_eq_a rsize )) (PreH4 : (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH5 : (0 <= rcap)) (PreH6 : (rcap <= INT_MAX)) (PreH7 : (0 <= an)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bn >= INT_MIN)) (PreH10 : (1 <= bn)) (PreH11 : (bn <= INT_MAX)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (an <= INT_MAX)) (PreH16 : (cmp <= INT_MAX)) (PreH17 : (bcap >= INT_MIN)) (PreH18 : (bsize >= INT_MIN)) (PreH19 : (rcap >= INT_MIN)) (PreH20 : (rsize >= INT_MIN)) (PreH21 : (an >= INT_MIN)) (PreH22 : (cmp >= INT_MIN)) (PreH23 : (cmp < 0)) (PreH24 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH25 : (cmp = (-1))) (PreH26 : (an = (Zabs (rsize)))) (PreH27 : (bn = (Zabs (bsize)))) (PreH28 : (same_sign za_r_eq_a rsize )) (PreH29 : (same_sign zb_r_eq_a bsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (0 <= rcap)) (PreH32 : (rcap <= INT_MAX)) (PreH33 : ((Zabs (bsize)) <= bcap)) (PreH34 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max ((Z.max (bn) (1))) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  EX (rcap_new: Z) ,
  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (a_pre = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg retval an bn )
  **  (UIntArray.undef_seg retval bn rcap_new )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
).

Definition mpz_abs_sub_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) 0 )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 >= 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = 0)) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) 0 )
).

Definition mpz_abs_sub_return_wit_1_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 >= 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = 0)) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) 0 )
.

Definition mpz_abs_sub_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH6 : (cmp < 0)) (PreH7 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH8 : (cmp = (-1))) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (bn <= rcap_new)) (PreH18 : (a = r_pre)) (PreH19 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval bn )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) (-retval) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= bn)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp < 0)) (PreH10 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = (-1))) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (bn <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval bn )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) (-retval) )
).

Definition mpz_abs_sub_return_wit_2_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= bn)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp < 0)) (PreH10 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = (-1))) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (bn <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval bn )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) (-retval) )
.

Definition mpz_abs_sub_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= an)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH6 : (cmp > 0)) (PreH7 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH8 : (cmp = 1)) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (an <= rcap_new)) (PreH18 : (a = r_pre)) (PreH19 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= an)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp > 0)) (PreH10 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = 1)) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (an <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
).

Definition mpz_abs_sub_return_wit_3_split_goal_spatial := 
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= an)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp > 0)) (PreH10 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = 1)) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (an <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD rptr_new val_r_out retval )
  **  (UIntArray.undef_seg rptr_new retval an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
|--
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
.

Definition mpz_abs_sub_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (INT_MIN < rsize)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (INT_MIN < bsize)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (0 <= rcap)) (PreH7 : (rcap <= INT_MAX)) (PreH8 : (0 <= bcap)) (PreH9 : (bcap <= INT_MAX)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : ((Zabs (bsize)) <= bcap)) (PreH13 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
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

Definition mpz_abs_sub_partial_solve_wit_1_aux := 
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

Definition mpz_abs_sub_partial_solve_wit_1 := mpz_abs_sub_partial_solve_wit_1_pure -> mpz_abs_sub_partial_solve_wit_1_aux.

Definition mpz_abs_sub_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (PreH1 : (retval = (Zabs (rsize)))) (PreH2 : (r_pre = a_pre)) (PreH3 : (INT_MIN < rsize)) (PreH4 : (rsize <= INT_MAX)) (PreH5 : (INT_MIN < bsize)) (PreH6 : (bsize <= INT_MAX)) (PreH7 : (0 <= rcap)) (PreH8 : (rcap <= INT_MAX)) (PreH9 : (0 <= bcap)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
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

Definition mpz_abs_sub_partial_solve_wit_2_aux := 
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

Definition mpz_abs_sub_partial_solve_wit_2 := mpz_abs_sub_partial_solve_wit_2_pure -> mpz_abs_sub_partial_solve_wit_2_aux.

Definition mpz_abs_sub_partial_solve_wit_3_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (bsize)))) (PreH2 : (retval = (Zabs (rsize)))) (PreH3 : (r_pre = a_pre)) (PreH4 : (INT_MIN < rsize)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (INT_MIN < bsize)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (0 <= rcap)) (PreH9 : (rcap <= INT_MAX)) (PreH10 : (0 <= bcap)) (PreH11 : (bcap <= INT_MAX)) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (same_sign za_r_eq_a rsize )) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
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
  “ (retval_2 >= 0) ” 
  &&  “ (retval >= 0) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval_2 = (Zabs (bsize)))) (PreH10 : (retval = (Zabs (rsize)))) (PreH11 : (r_pre = a_pre)) (PreH12 : (INT_MIN < rsize)) (PreH13 : (rsize <= INT_MAX)) (PreH14 : (INT_MIN < bsize)) (PreH15 : (bsize <= INT_MAX)) (PreH16 : (0 <= rcap)) (PreH17 : (rcap <= INT_MAX)) (PreH18 : (0 <= bcap)) (PreH19 : (bcap <= INT_MAX)) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (same_sign za_r_eq_a rsize )) (PreH22 : ((Zabs (bsize)) <= bcap)) (PreH23 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
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
  “ (retval >= 0) ” 
  &&  “ (retval_2 >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_3_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval_2 = (Zabs (bsize)))) (PreH10 : (retval = (Zabs (rsize)))) (PreH11 : (r_pre = a_pre)) (PreH12 : (INT_MIN < rsize)) (PreH13 : (rsize <= INT_MAX)) (PreH14 : (INT_MIN < bsize)) (PreH15 : (bsize <= INT_MAX)) (PreH16 : (0 <= rcap)) (PreH17 : (rcap <= INT_MAX)) (PreH18 : (0 <= bcap)) (PreH19 : (bcap <= INT_MAX)) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (same_sign za_r_eq_a rsize )) (PreH22 : ((Zabs (bsize)) <= bcap)) (PreH23 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
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
  “ (retval >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_3_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval_2 = (Zabs (bsize)))) (PreH10 : (retval = (Zabs (rsize)))) (PreH11 : (r_pre = a_pre)) (PreH12 : (INT_MIN < rsize)) (PreH13 : (rsize <= INT_MAX)) (PreH14 : (INT_MIN < bsize)) (PreH15 : (bsize <= INT_MAX)) (PreH16 : (0 <= rcap)) (PreH17 : (rcap <= INT_MAX)) (PreH18 : (0 <= bcap)) (PreH19 : (bcap <= INT_MAX)) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (same_sign za_r_eq_a rsize )) (PreH22 : ((Zabs (bsize)) <= bcap)) (PreH23 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
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
  “ (retval_2 >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (bsize)))) (PreH2 : (retval = (Zabs (rsize)))) (PreH3 : (r_pre = a_pre)) (PreH4 : (INT_MIN < rsize)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (INT_MIN < bsize)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (0 <= rcap)) (PreH9 : (rcap <= INT_MAX)) (PreH10 : (0 <= bcap)) (PreH11 : (bcap <= INT_MAX)) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (same_sign za_r_eq_a rsize )) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (same_sign zb_r_eq_a bsize )) ,
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
  “ (retval_2 >= 0) ” 
  &&  “ (retval >= 0) ” 
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
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) retval_2 )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_abs_sub_partial_solve_wit_3 := mpz_abs_sub_partial_solve_wit_3_pure -> mpz_abs_sub_partial_solve_wit_3_aux.

Definition mpz_abs_sub_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= bn)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an >= INT_MIN)) (PreH6 : (1 <= an)) (PreH7 : (an <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (bn <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = 1)) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (an >= 1) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ”
.

Definition mpz_abs_sub_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= bn)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an >= INT_MIN)) (PreH6 : (1 <= an)) (PreH7 : (an <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (bn <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = 1)) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (an >= 1) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (1 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_partial_solve_wit_4 := mpz_abs_sub_partial_solve_wit_4_pure -> mpz_abs_sub_partial_solve_wit_4_aux.

Definition mpz_abs_sub_partial_solve_wit_5_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = 1)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (an <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an > 0) ” 
  &&  “ (an >= bn) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (an >= bn) ” 
  &&  “ (an > 0) ” 
  &&  “ (bn >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (an >= bn) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (an > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
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

Definition mpz_abs_sub_partial_solve_wit_5_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = 1)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (an <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an > 0) ” 
  &&  “ (an >= bn) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (an <= rcap_new) ” 
  &&  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (mpd_store_Z UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_partial_solve_wit_5 := mpz_abs_sub_partial_solve_wit_5_pure -> mpz_abs_sub_partial_solve_wit_5_aux.

Definition mpz_abs_sub_partial_solve_wit_6_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp > 0)) (PreH6 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = 1)) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (an <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= an) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp > 0)) (PreH18 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = 1)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (an <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= an) ”
).

Definition mpz_abs_sub_partial_solve_wit_6_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp > 0)) (PreH18 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = 1)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (an <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= an) ”
.

Definition mpz_abs_sub_partial_solve_wit_6_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp > 0)) (PreH6 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = 1)) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (an <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= an) ” 
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (an <= rcap_new) ” 
  &&  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (mpd_store_Z UINT_MOD rptr_new val_r_out an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new an rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_partial_solve_wit_6 := mpz_abs_sub_partial_solve_wit_6_pure -> mpz_abs_sub_partial_solve_wit_6_aux.

Definition mpz_abs_sub_partial_solve_wit_7_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= an)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn >= INT_MIN)) (PreH6 : (1 <= bn)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (an <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (an >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = (-1))) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (bn >= 1) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= an)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn >= INT_MIN)) (PreH6 : (1 <= bn)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (an <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (an >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = (-1))) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (bn >= 1) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (0 <= an) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (bn >= INT_MIN) ” 
  &&  “ (1 <= bn) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (bcap <= INT_MAX) ” 
  &&  “ (bsize <= INT_MAX) ” 
  &&  “ (rsize <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (cmp <= INT_MAX) ” 
  &&  “ (bcap >= INT_MIN) ” 
  &&  “ (bsize >= INT_MIN) ” 
  &&  “ (rcap >= INT_MIN) ” 
  &&  “ (rsize >= INT_MIN) ” 
  &&  “ (an >= INT_MIN) ” 
  &&  “ (cmp >= INT_MIN) ” 
  &&  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (0 <= rcap) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_partial_solve_wit_7 := mpz_abs_sub_partial_solve_wit_7_pure -> mpz_abs_sub_partial_solve_wit_7_aux.

Definition mpz_abs_sub_partial_solve_wit_8_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp < 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = (-1))) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (bn <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn > 0) ” 
  &&  “ (bn >= an) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (bn >= an) ” 
  &&  “ (bn > 0) ” 
  &&  “ (an >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_8_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (bn >= an) ”
.

Definition mpz_abs_sub_partial_solve_wit_8_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (bn > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_8_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (an >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_8_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp < 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = (-1))) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (bn <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (mpd_store_Z_compact UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (rptr_new = rptr_new) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn > 0) ” 
  &&  “ (bn >= an) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (mpd_store_Z UINT_MOD rptr_new (Zabs (za_r_eq_a)) an )
  **  (UIntArray.undef_seg rptr_new an bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_partial_solve_wit_8 := mpz_abs_sub_partial_solve_wit_8_pure -> mpz_abs_sub_partial_solve_wit_8_aux.

Definition mpz_abs_sub_partial_solve_wit_9_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp < 0)) (PreH6 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = (-1))) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (bn <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= bn) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp < 0)) (PreH18 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = (-1))) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (bn <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= bn) ”
).

Definition mpz_abs_sub_partial_solve_wit_9_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp < 0)) (PreH18 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = (-1))) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (bn <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rptr_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= bn) ”
.

Definition mpz_abs_sub_partial_solve_wit_9_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp < 0)) (PreH6 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = (-1))) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (bn <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)) ,
  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (mpd_store_Z UINT_MOD rptr_new val_r_out bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  “ (0 <= bn) ” 
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (an = (Zabs (rsize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (same_sign za_r_eq_a rsize ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap_new) ” 
  &&  “ (0 <= rcap_new) ” 
  &&  “ (rcap_new <= INT_MAX) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (bn <= rcap_new) ” 
  &&  “ (a = r_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (mpd_store_Z UINT_MOD rptr_new val_r_out bn )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_new)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_new)
  **  (UIntArray.undef_seg rptr_new bn rcap_new )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (UIntArray.undef_seg bptr bn bcap )
.

Definition mpz_abs_sub_partial_solve_wit_9 := mpz_abs_sub_partial_solve_wit_9_pure -> mpz_abs_sub_partial_solve_wit_9_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_abs_sub_safety_wit_1 : mpz_abs_sub_safety_wit_1.
Axiom proof_of_mpz_abs_sub_safety_wit_2 : mpz_abs_sub_safety_wit_2.
Axiom proof_of_mpz_abs_sub_safety_wit_3 : mpz_abs_sub_safety_wit_3.
Axiom proof_of_mpz_abs_sub_safety_wit_4 : mpz_abs_sub_safety_wit_4.
Axiom proof_of_mpz_abs_sub_safety_wit_5 : mpz_abs_sub_safety_wit_5.
Axiom proof_of_mpz_abs_sub_safety_wit_6 : mpz_abs_sub_safety_wit_6.
Axiom proof_of_mpz_abs_sub_safety_wit_7 : mpz_abs_sub_safety_wit_7.
Axiom proof_of_mpz_abs_sub_safety_wit_8 : mpz_abs_sub_safety_wit_8.
Axiom proof_of_mpz_abs_sub_safety_wit_9 : mpz_abs_sub_safety_wit_9.
Axiom proof_of_mpz_abs_sub_safety_wit_10 : mpz_abs_sub_safety_wit_10.
Axiom proof_of_mpz_abs_sub_safety_wit_11 : mpz_abs_sub_safety_wit_11.
Axiom proof_of_mpz_abs_sub_safety_wit_12 : mpz_abs_sub_safety_wit_12.
Axiom proof_of_mpz_abs_sub_entail_wit_1 : mpz_abs_sub_entail_wit_1.
Axiom proof_of_mpz_abs_sub_entail_wit_2 : mpz_abs_sub_entail_wit_2.
Axiom proof_of_mpz_abs_sub_entail_wit_3 : mpz_abs_sub_entail_wit_3.
Axiom proof_of_mpz_abs_sub_entail_wit_4 : mpz_abs_sub_entail_wit_4.
Axiom proof_of_mpz_abs_sub_entail_wit_5 : mpz_abs_sub_entail_wit_5.
Axiom proof_of_mpz_abs_sub_entail_wit_6 : mpz_abs_sub_entail_wit_6.
Axiom proof_of_mpz_abs_sub_entail_wit_7 : mpz_abs_sub_entail_wit_7.
Axiom proof_of_mpz_abs_sub_entail_wit_8 : mpz_abs_sub_entail_wit_8.
Axiom proof_of_mpz_abs_sub_entail_wit_9 : mpz_abs_sub_entail_wit_9.
Axiom proof_of_mpz_abs_sub_entail_wit_10 : mpz_abs_sub_entail_wit_10.
Axiom proof_of_mpz_abs_sub_entail_wit_11 : mpz_abs_sub_entail_wit_11.
Axiom proof_of_mpz_abs_sub_return_wit_1 : mpz_abs_sub_return_wit_1.
Axiom proof_of_mpz_abs_sub_return_wit_2 : mpz_abs_sub_return_wit_2.
Axiom proof_of_mpz_abs_sub_return_wit_3 : mpz_abs_sub_return_wit_3.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_1_pure : mpz_abs_sub_partial_solve_wit_1_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_1 : mpz_abs_sub_partial_solve_wit_1.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2_pure : mpz_abs_sub_partial_solve_wit_2_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2 : mpz_abs_sub_partial_solve_wit_2.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_3_pure : mpz_abs_sub_partial_solve_wit_3_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_3 : mpz_abs_sub_partial_solve_wit_3.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4_pure : mpz_abs_sub_partial_solve_wit_4_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4 : mpz_abs_sub_partial_solve_wit_4.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5_pure : mpz_abs_sub_partial_solve_wit_5_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5 : mpz_abs_sub_partial_solve_wit_5.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6_pure : mpz_abs_sub_partial_solve_wit_6_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6 : mpz_abs_sub_partial_solve_wit_6.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7_pure : mpz_abs_sub_partial_solve_wit_7_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7 : mpz_abs_sub_partial_solve_wit_7.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8_pure : mpz_abs_sub_partial_solve_wit_8_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8 : mpz_abs_sub_partial_solve_wit_8.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9_pure : mpz_abs_sub_partial_solve_wit_9_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9 : mpz_abs_sub_partial_solve_wit_9.

End VC_Correct.
