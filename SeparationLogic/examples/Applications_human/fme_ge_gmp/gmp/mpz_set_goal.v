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

(*----- Function mpz_set -----*)

Definition mpz_set_safety_wit_1_eq := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre <> op_pre)) (PreH2 : (rop_pre = op_pre)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_Z op_pre z_eq )
|--
  “ False ”
.

Definition mpz_set_entail_wit_1_eq := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre = op_pre)) ,
  (store_Z op_pre z_eq )
|--
  “ (rop_pre = op_pre) ”
  &&  (store_Z op_pre z_eq )
.

Definition mpz_set_entail_wit_2_neq := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) ,
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
|--
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
.

Definition mpz_set_entail_wit_3_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (same_sign z_neq size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (rop_pre <> op_pre)) ,
  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old_neq )
|--
  EX (rptr: Z)  (optr: Z)  (rcap: Z)  (rsize: Z)  (ocap: Z)  (osize: Z) ,
  “ (retval = (Zabs (osize))) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (same_sign z_neq osize ) ” 
  &&  “ ((Zabs (osize)) <= ocap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) retval )
  **  (UIntArray.undef_seg optr retval ocap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old_neq size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign z_neq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old_neq)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
|--
  “ (cap_2 >= 0) ” 
  &&  “ (retval >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old_neq)) (Zabs (size_2)) )
).

Definition mpz_set_entail_wit_3_neq_split_goal_1 := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old_neq size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign z_neq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old_neq)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
|--
  “ (cap_2 >= 0) ”
.

Definition mpz_set_entail_wit_3_neq_split_goal_2 := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old_neq size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign z_neq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old_neq)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
|--
  “ (retval >= 0) ”
.

Definition mpz_set_entail_wit_3_neq_split_goal_spatial := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old_neq size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign z_neq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old_neq)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old_neq)) (Zabs (size_2)) )
.

Definition mpz_set_entail_wit_4_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr_2: Z) (osize_2: Z) (ocap_2: Z) (rsize_2: Z) (rcap_2: Z) (n: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign old_neq rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max (n) (rcap_2)))) (PreH3 : (n = (Zabs (osize_2)))) (PreH4 : (n >= 0)) (PreH5 : (same_sign z_neq osize_2 )) (PreH6 : ((Zabs (osize_2)) <= ocap_2)) (PreH7 : (same_sign old_neq rsize_2 )) (PreH8 : ((Zabs (rsize_2)) <= rcap_2)) (PreH9 : (rcap_2 >= 0)) (PreH10 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (old_neq)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max (n) (rcap_2)) )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr_2)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize_2)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap_2)
  **  (mpd_store_Z_compact UINT_MOD optr_2 (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr_2 n ocap_2 )
|--
  EX (optr: Z)  (rop__mp_d: Z)  (rop__mp_alloc: Z)  (rsize: Z)  (ocap: Z)  (rcap: Z)  (osize: Z) ,
  “ (n = (Zabs (osize))) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= (Z.max (n) (rcap))) ” 
  &&  “ (same_sign z_neq osize ) ” 
  &&  “ ((Zabs (osize)) <= ocap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop__mp_alloc = (Z.max (n) (rcap))) ” 
  &&  “ (rop__mp_d = retval) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rop__mp_alloc)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rop__mp_d)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
  **  (UIntArray.undef_full retval n )
  **  (UIntArray.undef_seg retval n (Z.max (n) (rcap)) )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr_2: Z) (osize_2: Z) (ocap_2: Z) (rsize_2: Z) (rcap_2: Z) (n: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign old_neq rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max (n) (rcap_2)))) (PreH3 : (n = (Zabs (osize_2)))) (PreH4 : (n >= 0)) (PreH5 : (same_sign z_neq osize_2 )) (PreH6 : ((Zabs (osize_2)) <= ocap_2)) (PreH7 : (same_sign old_neq rsize_2 )) (PreH8 : ((Zabs (rsize_2)) <= rcap_2)) (PreH9 : (rcap_2 >= 0)) (PreH10 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (old_neq)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max (n) (rcap_2)) )
  **  (mpd_store_Z_compact UINT_MOD optr_2 (Zabs (z_neq)) n )
|--
  EX (rcap: Z) ,
  “ (z_callee__mp_alloc = (Z.max (n) (rcap))) ” 
  &&  “ (z_callee__mp_alloc = (Z.max (n) (rcap))) ” 
  &&  “ (n = (Zabs (osize_2))) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= (Z.max (n) (rcap))) ” 
  &&  “ (same_sign z_neq osize_2 ) ” 
  &&  “ ((Zabs (osize_2)) <= ocap_2) ” 
  &&  “ (same_sign old_neq rsize_2 ) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD optr_2 (Zabs (z_neq)) n )
  **  (UIntArray.undef_full retval n )
  **  (UIntArray.undef_seg retval n (Z.max (n) (rcap)) )
).

Definition mpz_set_entail_wit_5_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (n: Z) (rop__mp_alloc_2: Z) (rop__mp_d_2: Z) (rp: Z) (optr_2: Z) (osize_2: Z) (ocap_2: Z) (rsize_2: Z) (rcap_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (z_neq)) n )) (PreH2 : (n = (Zabs (osize_2)))) (PreH3 : (n >= 0)) (PreH4 : (n <= (Z.max (n) (rcap_2)))) (PreH5 : (same_sign z_neq osize_2 )) (PreH6 : ((Zabs (osize_2)) <= ocap_2)) (PreH7 : (same_sign old_neq rsize_2 )) (PreH8 : ((Zabs (rsize_2)) <= rcap_2)) (PreH9 : (rcap_2 >= 0)) (PreH10 : (rop__mp_alloc_2 = (Z.max (n) (rcap_2)))) (PreH11 : (rop__mp_d_2 = rp)) (PreH12 : (rop_pre <> op_pre)) ,
  (mpd_store_Z UINT_MOD optr_2 (Zabs (z_neq)) n )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rop__mp_alloc_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rop__mp_d_2)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr_2)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize_2)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap_2)
  **  (UIntArray.undef_seg optr_2 n ocap_2 )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap_2)) )
|--
  EX (optr: Z)  (rop__mp_d: Z)  (rop__mp_alloc: Z)  (rsize: Z)  (ocap: Z)  (rcap: Z)  (osize: Z) ,
  “ (n = (Zabs (osize))) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= (Z.max (n) (rcap))) ” 
  &&  “ (same_sign z_neq osize ) ” 
  &&  “ ((Zabs (osize)) <= ocap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop__mp_alloc = (Z.max (n) (rcap))) ” 
  &&  “ (rop__mp_d = rp) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rop__mp_alloc)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rop__mp_d)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (n: Z) (rop__mp_alloc_2: Z) (rop__mp_d_2: Z) (rp: Z) (optr_2: Z) (osize_2: Z) (ocap_2: Z) (rsize_2: Z) (rcap_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (z_neq)) n )) (PreH2 : (n = (Zabs (osize_2)))) (PreH3 : (n >= 0)) (PreH4 : (n <= (Z.max (n) (rcap_2)))) (PreH5 : (same_sign z_neq osize_2 )) (PreH6 : ((Zabs (osize_2)) <= ocap_2)) (PreH7 : (same_sign old_neq rsize_2 )) (PreH8 : ((Zabs (rsize_2)) <= rcap_2)) (PreH9 : (rcap_2 >= 0)) (PreH10 : (rop__mp_alloc_2 = (Z.max (n) (rcap_2)))) (PreH11 : (rop__mp_d_2 = rp)) (PreH12 : (rop_pre <> op_pre)) ,
  (mpd_store_Z UINT_MOD optr_2 (Zabs (z_neq)) n )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap_2)) )
|--
  EX (rcap: Z) ,
  “ (rop__mp_d_2 = rp) ” 
  &&  “ (rop__mp_alloc_2 = (Z.max (n) (rcap))) ” 
  &&  “ (rop__mp_d_2 = rp) ” 
  &&  “ (rop__mp_alloc_2 = (Z.max (n) (rcap))) ” 
  &&  “ (n = (Zabs (osize_2))) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= (Z.max (n) (rcap))) ” 
  &&  “ (same_sign z_neq osize_2 ) ” 
  &&  “ ((Zabs (osize_2)) <= ocap_2) ” 
  &&  “ (same_sign old_neq rsize_2 ) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD optr_2 (Zabs (z_neq)) n )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
).

Definition mpz_set_return_wit_1_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr: Z) (osize: Z) (ocap: Z) (rsize: Z) (rcap: Z) (n: Z) (rop__mp_alloc: Z) (rop__mp_d: Z) (rp: Z) (PreH1 : (n = (Zabs (osize)))) (PreH2 : (n >= 0)) (PreH3 : (n <= (Z.max (n) (rcap)))) (PreH4 : (same_sign z_neq osize )) (PreH5 : ((Zabs (osize)) <= ocap)) (PreH6 : (same_sign old_neq rsize )) (PreH7 : ((Zabs (rsize)) <= rcap)) (PreH8 : (rcap >= 0)) (PreH9 : (rop__mp_alloc = (Z.max (n) (rcap)))) (PreH10 : (rop__mp_d = rp)) (PreH11 : (rop_pre <> op_pre)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rop__mp_alloc)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rop__mp_d)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
|--
  (store_Z rop_pre z_neq )
  **  (store_Z op_pre z_neq )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr: Z) (osize: Z) (ocap: Z) (rsize: Z) (rcap: Z) (n: Z) (rop__mp_alloc: Z) (rop__mp_d: Z) (rp: Z) (PreH1 : (n = (Zabs (osize)))) (PreH2 : (n >= 0)) (PreH3 : (n <= (Z.max (n) (rcap)))) (PreH4 : (same_sign z_neq osize )) (PreH5 : ((Zabs (osize)) <= ocap)) (PreH6 : (same_sign old_neq rsize )) (PreH7 : ((Zabs (rsize)) <= rcap)) (PreH8 : (rcap >= 0)) (PreH9 : (rop__mp_alloc = (Z.max (n) (rcap)))) (PreH10 : (rop__mp_d = rp)) (PreH11 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg rop__mp_d (Zabs (osize)) rop__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD rop__mp_d (Zabs (z_neq)) (Zabs (osize)) )
).

Definition mpz_set_return_wit_1_neq_split_goal_spatial := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr: Z) (osize: Z) (ocap: Z) (rsize: Z) (rcap: Z) (n: Z) (rop__mp_alloc: Z) (rop__mp_d: Z) (rp: Z) (PreH1 : (n = (Zabs (osize)))) (PreH2 : (n >= 0)) (PreH3 : (n <= (Z.max (n) (rcap)))) (PreH4 : (same_sign z_neq osize )) (PreH5 : ((Zabs (osize)) <= ocap)) (PreH6 : (same_sign old_neq rsize )) (PreH7 : ((Zabs (rsize)) <= rcap)) (PreH8 : (rcap >= 0)) (PreH9 : (rop__mp_alloc = (Z.max (n) (rcap)))) (PreH10 : (rop__mp_d = rp)) (PreH11 : (rop_pre <> op_pre)) ,
  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (mpd_store_Z UINT_MOD rp (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg rop__mp_d (Zabs (osize)) rop__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD rop__mp_d (Zabs (z_neq)) (Zabs (osize)) )
.

Definition mpz_set_return_wit_2_eq := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (rop_pre = op_pre)) ,
  (store_Z op_pre z_eq )
|--
  “ (rop_pre = op_pre) ”
  &&  (store_Z op_pre z_eq )
.

Definition mpz_set_return_wit_3_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (PreH1 : (rop_pre = op_pre)) ,
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
|--
  (store_Z rop_pre z_neq )
  **  (store_Z op_pre z_neq )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (PreH1 : (rop_pre = op_pre)) ,
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
|--
  (store_Z rop_pre z_neq )
  **  (store_Z op_pre z_neq )
).

Definition mpz_set_return_wit_3_neq_split_goal_spatial := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (PreH1 : (rop_pre = op_pre)) ,
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
|--
  (store_Z rop_pre z_neq )
  **  (store_Z op_pre z_neq )
.

Definition mpz_set_partial_solve_wit_1_neq := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (PreH1 : (rop_pre <> op_pre)) ,
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign z_neq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old_neq )
.

Definition mpz_set_partial_solve_wit_2_neq_pure := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign z_neq size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (rop_pre <> op_pre)) ,
  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_Z rop_pre old_neq )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign z_neq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (rop_pre <> op_pre)) ,
  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_Z rop_pre old_neq )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_set_partial_solve_wit_2_neq_pure_split_goal_1 := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign z_neq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (rop_pre <> op_pre)) ,
  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_Z rop_pre old_neq )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_set_partial_solve_wit_2_neq_aux := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign z_neq size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (rop_pre <> op_pre)) ,
  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old_neq )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign z_neq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_neq)) (Zabs (size)) )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old_neq )
.

Definition mpz_set_partial_solve_wit_2_neq := mpz_set_partial_solve_wit_2_neq_pure -> mpz_set_partial_solve_wit_2_neq_aux.

Definition mpz_set_partial_solve_wit_3_neq_pure := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr: Z) (osize: Z) (ocap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (n: Z) (PreH1 : (n = (Zabs (osize)))) (PreH2 : (n >= 0)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) (PreH5 : (same_sign old_neq rsize )) (PreH6 : ((Zabs (rsize)) <= rcap)) (PreH7 : (rcap >= 0)) (PreH8 : (rop_pre <> op_pre)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (osize)) <= INT_MAX) ” 
  &&  “ (rcap <= INT_MAX) ”
.

Definition mpz_set_partial_solve_wit_3_neq_aux := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (optr: Z) (osize: Z) (ocap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (n: Z) (PreH1 : (n = (Zabs (osize)))) (PreH2 : (n >= 0)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) (PreH5 : (same_sign old_neq rsize )) (PreH6 : ((Zabs (rsize)) <= rcap)) (PreH7 : (rcap >= 0)) (PreH8 : (rop_pre <> op_pre)) ,
  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ (rcap >= 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (osize)) <= INT_MAX) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (n = (Zabs (osize))) ” 
  &&  “ (n >= 0) ” 
  &&  “ (same_sign z_neq osize ) ” 
  &&  “ ((Zabs (osize)) <= ocap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
.

Definition mpz_set_partial_solve_wit_3_neq := mpz_set_partial_solve_wit_3_neq_pure -> mpz_set_partial_solve_wit_3_neq_aux.

Definition mpz_set_partial_solve_wit_4_neq := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) (n: Z) (rop__mp_alloc: Z) (rop__mp_d: Z) (rp: Z) (optr: Z) (osize: Z) (ocap: Z) (rsize: Z) (rcap: Z) (PreH1 : (n = (Zabs (osize)))) (PreH2 : (n >= 0)) (PreH3 : (n <= (Z.max (n) (rcap)))) (PreH4 : (same_sign z_neq osize )) (PreH5 : ((Zabs (osize)) <= ocap)) (PreH6 : (same_sign old_neq rsize )) (PreH7 : ((Zabs (rsize)) <= rcap)) (PreH8 : (rcap >= 0)) (PreH9 : (rop__mp_alloc = (Z.max (n) (rcap)))) (PreH10 : (rop__mp_d = rp)) (PreH11 : (rop_pre <> op_pre)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rop__mp_alloc)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rop__mp_d)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_seg optr n ocap )
  **  (UIntArray.undef_full rp n )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
|--
  “ (is_compact_Z UINT_MOD (Zabs (z_neq)) n ) ” 
  &&  “ (n = (Zabs (osize))) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= (Z.max (n) (rcap))) ” 
  &&  “ (same_sign z_neq osize ) ” 
  &&  “ ((Zabs (osize)) <= ocap) ” 
  &&  “ (same_sign old_neq rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rop__mp_alloc = (Z.max (n) (rcap))) ” 
  &&  “ (rop__mp_d = rp) ” 
  &&  “ (rop_pre <> op_pre) ”
  &&  (mpd_store_Z UINT_MOD optr (Zabs (z_neq)) n )
  **  (UIntArray.undef_full rp n )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rop__mp_alloc)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rop__mp_d)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (UIntArray.undef_seg optr n ocap )
  **  (UIntArray.undef_seg rp n (Z.max (n) (rcap)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_set_safety_wit_1_eq : mpz_set_safety_wit_1_eq.
Axiom proof_of_mpz_set_entail_wit_1_eq : mpz_set_entail_wit_1_eq.
Axiom proof_of_mpz_set_entail_wit_2_neq : mpz_set_entail_wit_2_neq.
Axiom proof_of_mpz_set_entail_wit_3_neq : mpz_set_entail_wit_3_neq.
Axiom proof_of_mpz_set_entail_wit_4_neq : mpz_set_entail_wit_4_neq.
Axiom proof_of_mpz_set_entail_wit_5_neq : mpz_set_entail_wit_5_neq.
Axiom proof_of_mpz_set_return_wit_1_neq : mpz_set_return_wit_1_neq.
Axiom proof_of_mpz_set_return_wit_2_eq : mpz_set_return_wit_2_eq.
Axiom proof_of_mpz_set_return_wit_3_neq : mpz_set_return_wit_3_neq.
Axiom proof_of_mpz_set_partial_solve_wit_1_neq : mpz_set_partial_solve_wit_1_neq.
Axiom proof_of_mpz_set_partial_solve_wit_2_neq_pure : mpz_set_partial_solve_wit_2_neq_pure.
Axiom proof_of_mpz_set_partial_solve_wit_2_neq : mpz_set_partial_solve_wit_2_neq.
Axiom proof_of_mpz_set_partial_solve_wit_3_neq_pure : mpz_set_partial_solve_wit_3_neq_pure.
Axiom proof_of_mpz_set_partial_solve_wit_3_neq : mpz_set_partial_solve_wit_3_neq.
Axiom proof_of_mpz_set_partial_solve_wit_4_neq : mpz_set_partial_solve_wit_4_neq.

End VC_Correct.
