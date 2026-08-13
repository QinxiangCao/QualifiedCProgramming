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

(*----- Function mpz_sub -----*)

Definition mpz_sub_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= cap)) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zabs (rn_v)) <= cap)) (PreH5 : ((Zabs (bsize)) <= bcap)) (PreH6 : ((Z.lxor old_size bsize) >= 0)) (PreH7 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH8 : (same_sign za_r_eq_a old_size )) (PreH9 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rn_v <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rn_v <> (INT_MIN)) ”
).

Definition mpz_sub_safety_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rn_v <> (INT_MIN)) ”
.

Definition mpz_sub_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= cap)) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zabs (rn_v)) <= cap)) (PreH5 : ((Zabs (bsize)) <= bcap)) (PreH6 : ((Z.lxor old_size bsize) < 0)) (PreH7 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH8 : (same_sign za_r_eq_a old_size )) (PreH9 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rn_v <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rn_v <> (INT_MIN)) ”
).

Definition mpz_sub_safety_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (rn_v <> (INT_MIN)) ”
.

Definition mpz_sub_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_3)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap_2)) (PreH6 : (r_pre = a_pre)) ,
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (bptr: Z)  (ptr: Z)  (old_size: Z)  (bcap: Z)  (bsize: Z)  (cap: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (retval)) <= cap) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Z.lxor old_size bsize) >= 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (retval)) )
  **  (UIntArray.undef_seg ptr (Zabs (retval)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (ptr_2: Z) (size_3: Z) (cap_4: Z) (PreH1 : (same_sign zb_r_eq_a size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_4)) (PreH3 : ((Z.lxor size size_2) >= 0)) (PreH4 : (same_sign zb_r_eq_a size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_3)) (PreH6 : (same_sign za_r_eq_a size )) (PreH7 : ((Zabs (size)) <= cap_2)) (PreH8 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_3)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
|--
  EX (ptr: Z)  (old_size: Z)  (cap: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (retval)) <= cap) ” 
  &&  “ ((Zabs (size_3)) <= cap_4) ” 
  &&  “ ((Z.lxor old_size size_3) >= 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a size_3 ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (retval)) )
  **  (UIntArray.undef_seg ptr (Zabs (retval)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_3)) )
).

Definition mpz_sub_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_3)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap_2)) (PreH6 : (r_pre = a_pre)) ,
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) retval )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (bptr: Z)  (ptr: Z)  (old_size: Z)  (bcap: Z)  (bsize: Z)  (cap: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (retval)) <= cap) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Z.lxor old_size bsize) < 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) retval ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (retval)) )
  **  (UIntArray.undef_seg ptr (Zabs (retval)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (ptr_2: Z) (size_3: Z) (cap_4: Z) (PreH1 : (same_sign zb_r_eq_a size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_4)) (PreH3 : ((Z.lxor size size_2) < 0)) (PreH4 : (same_sign zb_r_eq_a size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_3)) (PreH6 : (same_sign za_r_eq_a size )) (PreH7 : ((Zabs (size)) <= cap_2)) (PreH8 : (r_pre = a_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_3)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) retval )
|--
  EX (ptr: Z)  (old_size: Z)  (cap: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (retval)) <= cap) ” 
  &&  “ ((Zabs (size_3)) <= cap_4) ” 
  &&  “ ((Z.lxor old_size size_3) < 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) retval ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a size_3 ) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (retval)) )
  **  (UIntArray.undef_seg ptr (Zabs (retval)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_3)) )
).

Definition mpz_sub_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  (store_Z a_pre (za_r_eq_a - zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (rn_v <= INT_MAX)) (PreH2 : (rn_v >= INT_MIN)) (PreH3 : (old_size >= 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) >= 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn_v)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z) ,
  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign (za_r_eq_a - zb_r_eq_a ) size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a - zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_sub_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn_v))
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  (store_Z a_pre (za_r_eq_a - zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : ((-rn_v) <= INT_MAX)) (PreH2 : ((-rn_v) >= INT_MIN)) (PreH3 : (old_size < 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) >= 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn_v))
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z) ,
  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign (za_r_eq_a - zb_r_eq_a ) size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a - zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_sub_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn_v)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  (store_Z a_pre (za_r_eq_a - zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (rn_v <= INT_MAX)) (PreH2 : (rn_v >= INT_MIN)) (PreH3 : (old_size >= 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) < 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn_v)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z) ,
  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign (za_r_eq_a - zb_r_eq_a ) size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a - zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_sub_return_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn_v))
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  (store_Z a_pre (za_r_eq_a - zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : ((-rn_v) <= INT_MAX)) (PreH2 : ((-rn_v) >= INT_MIN)) (PreH3 : (old_size < 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) < 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn_v))
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z) ,
  “ (same_sign zb_r_eq_a bsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ (same_sign (za_r_eq_a - zb_r_eq_a ) size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a - zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_sub_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (PreH1 : (r_pre = a_pre)) ,
  (store_Z a_pre za_r_eq_a )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (ptr: Z)  (size: Z)  (cap: Z) ,
  “ (same_sign za_r_eq_a size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre zb_r_eq_a )
.

Definition mpz_sub_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign za_r_eq_a size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (r_pre = a_pre)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (ptr_2: Z)  (size_2: Z)  (cap_2: Z) ,
  “ (same_sign zb_r_eq_a size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign za_r_eq_a size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_sub_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (r_pre = a_pre) ”
.

Definition mpz_sub_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (r_pre = a_pre) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign zb_r_eq_a size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign za_r_eq_a size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_Z a_pre za_r_eq_a )
  **  (store_Z b_pre zb_r_eq_a )
.

Definition mpz_sub_partial_solve_wit_3 := mpz_sub_partial_solve_wit_3_pure -> mpz_sub_partial_solve_wit_3_aux.

Definition mpz_sub_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (r_pre = a_pre) ”
.

Definition mpz_sub_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (r_pre = a_pre) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign zb_r_eq_a size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign za_r_eq_a size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_Z a_pre za_r_eq_a )
  **  (store_Z b_pre zb_r_eq_a )
.

Definition mpz_sub_partial_solve_wit_4 := mpz_sub_partial_solve_wit_4_pure -> mpz_sub_partial_solve_wit_4_aux.

Definition mpz_sub_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (old_size >= 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (rn_v)) <= cap) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Z.lxor old_size bsize) >= 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_sub_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (old_size < 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (rn_v)) <= cap) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Z.lxor old_size bsize) >= 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_sub_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (old_size >= 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (rn_v)) <= cap) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Z.lxor old_size bsize) < 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Definition mpz_sub_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (zb_r_eq_a: Z) (za_r_eq_a: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
|--
  “ (old_size < 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (rn_v)) <= cap) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ” 
  &&  “ ((Z.lxor old_size bsize) < 0) ” 
  &&  “ (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v ) ” 
  &&  “ (same_sign za_r_eq_a old_size ) ” 
  &&  “ (same_sign zb_r_eq_a bsize ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_sub_safety_wit_1 : mpz_sub_safety_wit_1.
Axiom proof_of_mpz_sub_safety_wit_2 : mpz_sub_safety_wit_2.
Axiom proof_of_mpz_sub_safety_wit_3 : mpz_sub_safety_wit_3.
Axiom proof_of_mpz_sub_safety_wit_4 : mpz_sub_safety_wit_4.
Axiom proof_of_mpz_sub_safety_wit_5 : mpz_sub_safety_wit_5.
Axiom proof_of_mpz_sub_entail_wit_1 : mpz_sub_entail_wit_1.
Axiom proof_of_mpz_sub_entail_wit_2 : mpz_sub_entail_wit_2.
Axiom proof_of_mpz_sub_return_wit_1 : mpz_sub_return_wit_1.
Axiom proof_of_mpz_sub_return_wit_2 : mpz_sub_return_wit_2.
Axiom proof_of_mpz_sub_return_wit_3 : mpz_sub_return_wit_3.
Axiom proof_of_mpz_sub_return_wit_4 : mpz_sub_return_wit_4.
Axiom proof_of_mpz_sub_partial_solve_wit_1 : mpz_sub_partial_solve_wit_1.
Axiom proof_of_mpz_sub_partial_solve_wit_2 : mpz_sub_partial_solve_wit_2.
Axiom proof_of_mpz_sub_partial_solve_wit_3_pure : mpz_sub_partial_solve_wit_3_pure.
Axiom proof_of_mpz_sub_partial_solve_wit_3 : mpz_sub_partial_solve_wit_3.
Axiom proof_of_mpz_sub_partial_solve_wit_4_pure : mpz_sub_partial_solve_wit_4_pure.
Axiom proof_of_mpz_sub_partial_solve_wit_4 : mpz_sub_partial_solve_wit_4.
Axiom proof_of_mpz_sub_partial_solve_wit_5 : mpz_sub_partial_solve_wit_5.
Axiom proof_of_mpz_sub_partial_solve_wit_6 : mpz_sub_partial_solve_wit_6.
Axiom proof_of_mpz_sub_partial_solve_wit_7 : mpz_sub_partial_solve_wit_7.
Axiom proof_of_mpz_sub_partial_solve_wit_8 : mpz_sub_partial_solve_wit_8.

End VC_Correct.
