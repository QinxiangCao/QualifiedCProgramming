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

(*----- Function mpz_cmp -----*)

Definition mpz_cmp_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (a_size: Z) (acap: Z) (bptr: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size < b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> a_size)
  **  ((( &( "bsize" ) )) # Int  |-> b_size)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr (Zabs (a_size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr (Zabs (b_size)) bcap )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpz_cmp_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (a_size: Z) (acap: Z) (bptr: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size < b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> a_size)
  **  ((( &( "bsize" ) )) # Int  |-> b_size)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr (Zabs (a_size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr (Zabs (b_size)) bcap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_cmp_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (a_size: Z) (acap: Z) (bptr: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size >= b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> a_size)
  **  ((( &( "bsize" ) )) # Int  |-> b_size)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr (Zabs (a_size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr (Zabs (b_size)) bcap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_cmp_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (a_size: Z) (acap: Z) (bptr: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size = b_size)) (PreH2 : (same_sign za_neq a_size )) (PreH3 : ((Zabs (a_size)) <= acap)) (PreH4 : (same_sign zb_neq b_size )) (PreH5 : ((Zabs (b_size)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> a_size)
  **  ((( &( "bsize" ) )) # Int  |-> b_size)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr (Zabs (a_size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr (Zabs (b_size)) bcap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_cmp_safety_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (asize < 0)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> asize)
  **  ((( &( "bsize" ) )) # Int  |-> bsize)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (asize <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (asize < 0)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> asize)
  **  ((( &( "bsize" ) )) # Int  |-> bsize)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (asize <> (INT_MIN)) ”
).

Definition mpz_cmp_safety_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (asize < 0)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> asize)
  **  ((( &( "bsize" ) )) # Int  |-> bsize)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (asize <> (INT_MIN)) ”
.

Definition mpz_cmp_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_neq size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_neq size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_neq)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_neq)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  EX (bptr: Z)  (aptr: Z)  (bcap: Z)  (acap: Z) ,
  “ (same_sign za_neq size ) ” 
  &&  “ ((Zabs (size)) <= acap) ” 
  &&  “ (same_sign zb_neq size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= bcap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (size)) )
  **  (UIntArray.undef_seg aptr (Zabs (size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg bptr (Zabs (size_2)) bcap )
.

Definition mpz_cmp_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr_2: Z) (a_size: Z) (acap_2: Z) (bptr_2: Z) (b_size: Z) (bcap_2: Z) (PreH1 : (a_size >= 0)) (PreH2 : (a_size = b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap_2)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap_2)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap_2)
  **  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr_2 (Zabs (a_size)) acap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap_2)
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr_2 (Zabs (b_size)) bcap_2 )
|--
  EX (bptr: Z)  (aptr: Z)  (bcap: Z)  (acap: Z) ,
  “ (a_size = b_size) ” 
  &&  “ (0 <= a_size) ” 
  &&  “ (same_sign za_neq a_size ) ” 
  &&  “ ((Zabs (a_size)) <= acap) ” 
  &&  “ (same_sign zb_neq b_size ) ” 
  &&  “ ((Zabs (b_size)) <= bcap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) a_size )
  **  (UIntArray.undef_seg aptr a_size acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) a_size )
  **  (UIntArray.undef_seg bptr a_size bcap )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr_2: Z) (a_size: Z) (acap_2: Z) (bptr_2: Z) (b_size: Z) (bcap_2: Z) (PreH1 : (a_size >= 0)) (PreH2 : (a_size = b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap_2)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap_2)) ,
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr_2 (Zabs (a_size)) acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr_2 (Zabs (b_size)) bcap_2 )
|--
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) a_size )
  **  (UIntArray.undef_seg aptr_2 a_size acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) a_size )
  **  (UIntArray.undef_seg bptr_2 a_size bcap_2 )
).

Definition mpz_cmp_entail_wit_2_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr_2: Z) (a_size: Z) (acap_2: Z) (bptr_2: Z) (b_size: Z) (bcap_2: Z) (PreH1 : (a_size >= 0)) (PreH2 : (a_size = b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap_2)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap_2)) ,
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr_2 (Zabs (a_size)) acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr_2 (Zabs (b_size)) bcap_2 )
|--
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) a_size )
  **  (UIntArray.undef_seg aptr_2 a_size acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) a_size )
  **  (UIntArray.undef_seg bptr_2 a_size bcap_2 )
.

Definition mpz_cmp_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr_2: Z) (a_size: Z) (acap_2: Z) (bptr_2: Z) (b_size: Z) (bcap_2: Z) (PreH1 : (a_size < 0)) (PreH2 : (a_size = b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap_2)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap_2)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap_2)
  **  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr_2 (Zabs (a_size)) acap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap_2)
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr_2 (Zabs (b_size)) bcap_2 )
|--
  EX (bptr: Z)  (aptr: Z)  (bcap: Z)  (acap: Z) ,
  “ (a_size = b_size) ” 
  &&  “ (a_size < 0) ” 
  &&  “ (same_sign za_neq a_size ) ” 
  &&  “ ((Zabs (a_size)) <= acap) ” 
  &&  “ (same_sign zb_neq b_size ) ” 
  &&  “ ((Zabs (b_size)) <= bcap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-a_size) )
  **  (UIntArray.undef_seg aptr (-a_size) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-a_size) )
  **  (UIntArray.undef_seg bptr (-a_size) bcap )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr_2: Z) (a_size: Z) (acap_2: Z) (bptr_2: Z) (b_size: Z) (bcap_2: Z) (PreH1 : (a_size < 0)) (PreH2 : (a_size = b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap_2)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap_2)) ,
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr_2 (Zabs (a_size)) acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr_2 (Zabs (b_size)) bcap_2 )
|--
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (-a_size) )
  **  (UIntArray.undef_seg aptr_2 (-a_size) acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (-a_size) )
  **  (UIntArray.undef_seg bptr_2 (-a_size) bcap_2 )
).

Definition mpz_cmp_entail_wit_3_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr_2: Z) (a_size: Z) (acap_2: Z) (bptr_2: Z) (b_size: Z) (bcap_2: Z) (PreH1 : (a_size < 0)) (PreH2 : (a_size = b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap_2)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap_2)) ,
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr_2 (Zabs (a_size)) acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr_2 (Zabs (b_size)) bcap_2 )
|--
  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (za_neq)) (-a_size) )
  **  (UIntArray.undef_seg aptr_2 (-a_size) acap_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (zb_neq)) (-a_size) )
  **  (UIntArray.undef_seg bptr_2 (-a_size) bcap_2 )
.

Definition mpz_cmp_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) < (Zabs (za_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq < zb_neq) ” 
  &&  “ (retval = (-1)) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) < (Zabs (za_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq < zb_neq) ”
  &&  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
).

Definition mpz_cmp_return_wit_1_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) < (Zabs (za_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq < zb_neq) ”
.

Definition mpz_cmp_return_wit_1_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) < (Zabs (za_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
.

Definition mpz_cmp_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) = (Zabs (za_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq = zb_neq) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) = (Zabs (za_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq = zb_neq) ”
  &&  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
).

Definition mpz_cmp_return_wit_2_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) = (Zabs (za_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq = zb_neq) ”
.

Definition mpz_cmp_return_wit_2_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) = (Zabs (za_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
.

Definition mpz_cmp_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) > (Zabs (za_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq > zb_neq) ” 
  &&  “ (retval = 1) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) > (Zabs (za_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq > zb_neq) ”
  &&  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
).

Definition mpz_cmp_return_wit_3_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) > (Zabs (za_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (za_neq > zb_neq) ”
.

Definition mpz_cmp_return_wit_3_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (zb_neq)) > (Zabs (za_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (asize < 0)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
.

Definition mpz_cmp_return_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) < (Zabs (zb_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr asize acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq < zb_neq) ” 
  &&  “ (retval = (-1)) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) < (Zabs (zb_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq < zb_neq) ”
  &&  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
).

Definition mpz_cmp_return_wit_4_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) < (Zabs (zb_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq < zb_neq) ”
.

Definition mpz_cmp_return_wit_4_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) < (Zabs (zb_neq)))) (PreH2 : (retval = (-1))) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
.

Definition mpz_cmp_return_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) = (Zabs (zb_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr asize acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq = zb_neq) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) = (Zabs (zb_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq = zb_neq) ”
  &&  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
).

Definition mpz_cmp_return_wit_5_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) = (Zabs (zb_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq = zb_neq) ”
.

Definition mpz_cmp_return_wit_5_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) = (Zabs (zb_neq)))) (PreH2 : (retval = 0)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
.

Definition mpz_cmp_return_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) > (Zabs (zb_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr asize acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq > zb_neq) ” 
  &&  “ (retval = 1) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) > (Zabs (zb_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq > zb_neq) ”
  &&  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
).

Definition mpz_cmp_return_wit_6_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) > (Zabs (zb_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (za_neq > zb_neq) ”
.

Definition mpz_cmp_return_wit_6_split_goal_spatial := 
forall (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (retval: Z) (PreH1 : ((Zabs (za_neq)) > (Zabs (zb_neq)))) (PreH2 : (retval = 1)) (PreH3 : (asize = bsize)) (PreH4 : (0 <= asize)) (PreH5 : (same_sign za_neq asize )) (PreH6 : ((Zabs (asize)) <= acap)) (PreH7 : (same_sign zb_neq bsize )) (PreH8 : ((Zabs (bsize)) <= bcap)) ,
  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  (UIntArray.undef_seg bptr (Zabs (bsize)) bcap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg aptr (Zabs (asize)) acap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (asize)) )
.

Definition mpz_cmp_return_wit_7 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (a_size: Z) (acap: Z) (bptr: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size < b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr (Zabs (a_size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr (Zabs (b_size)) bcap )
|--
  “ (za_neq < zb_neq) ” 
  &&  “ ((-1) = (-1)) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (a_size: Z) (acap: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size < b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  TT && emp 
|--
  “ (za_neq < zb_neq) ”
  &&  emp
).

Definition mpz_cmp_return_wit_7_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (a_size: Z) (acap: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size < b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  (za_neq < zb_neq)
.

Definition mpz_cmp_return_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (a_size: Z) (acap: Z) (bptr: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size >= b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (Zabs (a_size)) )
  **  (UIntArray.undef_seg aptr (Zabs (a_size)) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (Zabs (b_size)) )
  **  (UIntArray.undef_seg bptr (Zabs (b_size)) bcap )
|--
  “ (za_neq > zb_neq) ” 
  &&  “ (1 = 1) ”
  &&  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
) \/
(
forall (zb_neq: Z) (za_neq: Z) (a_size: Z) (acap: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size >= b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  TT && emp 
|--
  “ (za_neq > zb_neq) ”
  &&  emp
).

Definition mpz_cmp_return_wit_8_split_goal_1 := 
forall (zb_neq: Z) (za_neq: Z) (a_size: Z) (acap: Z) (b_size: Z) (bcap: Z) (PreH1 : (a_size >= b_size)) (PreH2 : (a_size <> b_size)) (PreH3 : (same_sign za_neq a_size )) (PreH4 : ((Zabs (a_size)) <= acap)) (PreH5 : (same_sign zb_neq b_size )) (PreH6 : ((Zabs (b_size)) <= bcap)) ,
  (za_neq > zb_neq)
.

Definition mpz_cmp_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) ,
  (store_Z a_pre za_neq )
  **  (store_Z b_pre zb_neq )
|--
  EX (ptr: Z)  (size: Z)  (cap: Z) ,
  “ (same_sign za_neq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_neq)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre zb_neq )
.

Definition mpz_cmp_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign za_neq size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_neq)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre zb_neq )
|--
  EX (ptr_2: Z)  (size_2: Z)  (cap_2: Z) ,
  “ (same_sign zb_neq size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign za_neq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_neq)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_neq)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_cmp_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (0 <= asize)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> asize)
  **  ((( &( "bsize" ) )) # Int  |-> bsize)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (0 <= asize) ”
.

Definition mpz_cmp_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (0 <= asize)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (UIntArray.undef_seg aptr asize acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  (UIntArray.undef_seg bptr asize bcap )
|--
  “ (0 <= asize) ” 
  &&  “ (asize = bsize) ” 
  &&  “ (0 <= asize) ” 
  &&  “ (same_sign za_neq asize ) ” 
  &&  “ ((Zabs (asize)) <= acap) ” 
  &&  “ (same_sign zb_neq bsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) asize )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) asize )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr asize acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr asize bcap )
.

Definition mpz_cmp_partial_solve_wit_3 := mpz_cmp_partial_solve_wit_3_pure -> mpz_cmp_partial_solve_wit_3_aux.

Definition mpz_cmp_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (asize < 0)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((( &( "asize" ) )) # Int  |-> asize)
  **  ((( &( "bsize" ) )) # Int  |-> bsize)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (0 <= (-asize)) ”
.

Definition mpz_cmp_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (zb_neq: Z) (za_neq: Z) (aptr: Z) (acap: Z) (bptr: Z) (bcap: Z) (asize: Z) (bsize: Z) (PreH1 : (asize = bsize)) (PreH2 : (asize < 0)) (PreH3 : (same_sign za_neq asize )) (PreH4 : ((Zabs (asize)) <= acap)) (PreH5 : (same_sign zb_neq bsize )) (PreH6 : ((Zabs (bsize)) <= bcap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (UIntArray.undef_seg bptr (-asize) bcap )
|--
  “ (0 <= (-asize)) ” 
  &&  “ (asize = bsize) ” 
  &&  “ (asize < 0) ” 
  &&  “ (same_sign za_neq asize ) ” 
  &&  “ ((Zabs (asize)) <= acap) ” 
  &&  “ (same_sign zb_neq bsize ) ” 
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_neq)) (-asize) )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (za_neq)) (-asize) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  (UIntArray.undef_seg aptr (-asize) acap )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg bptr (-asize) bcap )
.

Definition mpz_cmp_partial_solve_wit_4 := mpz_cmp_partial_solve_wit_4_pure -> mpz_cmp_partial_solve_wit_4_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_cmp_safety_wit_1 : mpz_cmp_safety_wit_1.
Axiom proof_of_mpz_cmp_safety_wit_2 : mpz_cmp_safety_wit_2.
Axiom proof_of_mpz_cmp_safety_wit_3 : mpz_cmp_safety_wit_3.
Axiom proof_of_mpz_cmp_safety_wit_4 : mpz_cmp_safety_wit_4.
Axiom proof_of_mpz_cmp_safety_wit_5 : mpz_cmp_safety_wit_5.
Axiom proof_of_mpz_cmp_entail_wit_1 : mpz_cmp_entail_wit_1.
Axiom proof_of_mpz_cmp_entail_wit_2 : mpz_cmp_entail_wit_2.
Axiom proof_of_mpz_cmp_entail_wit_3 : mpz_cmp_entail_wit_3.
Axiom proof_of_mpz_cmp_return_wit_1 : mpz_cmp_return_wit_1.
Axiom proof_of_mpz_cmp_return_wit_2 : mpz_cmp_return_wit_2.
Axiom proof_of_mpz_cmp_return_wit_3 : mpz_cmp_return_wit_3.
Axiom proof_of_mpz_cmp_return_wit_4 : mpz_cmp_return_wit_4.
Axiom proof_of_mpz_cmp_return_wit_5 : mpz_cmp_return_wit_5.
Axiom proof_of_mpz_cmp_return_wit_6 : mpz_cmp_return_wit_6.
Axiom proof_of_mpz_cmp_return_wit_7 : mpz_cmp_return_wit_7.
Axiom proof_of_mpz_cmp_return_wit_8 : mpz_cmp_return_wit_8.
Axiom proof_of_mpz_cmp_partial_solve_wit_1 : mpz_cmp_partial_solve_wit_1.
Axiom proof_of_mpz_cmp_partial_solve_wit_2 : mpz_cmp_partial_solve_wit_2.
Axiom proof_of_mpz_cmp_partial_solve_wit_3_pure : mpz_cmp_partial_solve_wit_3_pure.
Axiom proof_of_mpz_cmp_partial_solve_wit_3 : mpz_cmp_partial_solve_wit_3.
Axiom proof_of_mpz_cmp_partial_solve_wit_4_pure : mpz_cmp_partial_solve_wit_4_pure.
Axiom proof_of_mpz_cmp_partial_solve_wit_4 : mpz_cmp_partial_solve_wit_4.

End VC_Correct.
