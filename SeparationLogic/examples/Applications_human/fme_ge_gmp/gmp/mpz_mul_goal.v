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

(*----- Function mpz_mul -----*)

Definition mpz_mul_safety_wit_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign z2 size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign z1 size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign z2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign z1 size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_3 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign z2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign z1 size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_4 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (size <> 0)) (PreH3 : (same_sign z2 size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (same_sign z1 size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_5 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (size <> 0)) (PreH3 : (same_sign z2 size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (same_sign z1 size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_6 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < 0)) (PreH2 : (size_2 <> 0)) (PreH3 : (size <> 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_7 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <= 0)) (PreH2 : (size < 0)) (PreH3 : (size_2 <> 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_8 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size >= 0)) (PreH2 : (size_2 <> 0)) (PreH3 : (size <> 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_9 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size > 0)) (PreH2 : (size_2 <= 0)) (PreH3 : (size < 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ False ”
.

Definition mpz_mul_safety_wit_10 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size <= 0)) (PreH2 : (size >= 0)) (PreH3 : (size_2 <> 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ False ”
.

Definition mpz_mul_safety_wit_11 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size > 0)) (PreH2 : (size >= 0)) (PreH3 : (size_2 <> 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_12 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 > 0)) (PreH2 : (size < 0)) (PreH3 : (size_2 <> 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_safety_wit_13 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 < 0)) (PreH2 : (size > 0)) (PreH3 : (size >= 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_safety_wit_14 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 >= 0)) (PreH2 : (size > 0)) (PreH3 : (size >= 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_15 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size <= 0)) (PreH2 : (size_2 <= 0)) (PreH3 : (size < 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_16 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 > 0)) (PreH4 : (size < 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (size <> 0)) (PreH7 : (same_sign z2 size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign z1 size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 > 0)) (PreH4 : (size < 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (size <> 0)) (PreH7 : (same_sign z2 size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign z1 size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
).

Definition mpz_mul_safety_wit_16_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 > 0)) (PreH4 : (size < 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (size <> 0)) (PreH7 : (same_sign z2 size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign z1 size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ”
.

Definition mpz_mul_safety_wit_16_split_goal_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 > 0)) (PreH4 : (size < 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (size <> 0)) (PreH7 : (same_sign z2 size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign z1 size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((INT_MIN) <= (retval + retval_2 )) ”
.

Definition mpz_mul_safety_wit_17 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 < 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 < 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
).

Definition mpz_mul_safety_wit_17_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 < 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ”
.

Definition mpz_mul_safety_wit_17_split_goal_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 < 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((INT_MIN) <= (retval + retval_2 )) ”
.

Definition mpz_mul_safety_wit_18 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 >= 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 >= 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
).

Definition mpz_mul_safety_wit_18_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 >= 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ”
.

Definition mpz_mul_safety_wit_18_split_goal_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 >= 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((INT_MIN) <= (retval + retval_2 )) ”
.

Definition mpz_mul_safety_wit_19 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <= 0)) (PreH4 : (size_2 <= 0)) (PreH5 : (size < 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <= 0)) (PreH4 : (size_2 <= 0)) (PreH5 : (size < 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
).

Definition mpz_mul_safety_wit_19_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <= 0)) (PreH4 : (size_2 <= 0)) (PreH5 : (size < 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((retval + retval_2 ) <= INT_MAX) ”
.

Definition mpz_mul_safety_wit_19_split_goal_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <= 0)) (PreH4 : (size_2 <= 0)) (PreH5 : (size < 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> retval_2)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ ((INT_MIN) <= (retval + retval_2 )) ”
.

Definition mpz_mul_safety_wit_20 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (rcap >= 0)) (PreH20 : (rcap <= INT_MAX)) (PreH21 : ((Zlength (l1)) = un)) (PreH22 : ((Zlength (l2)) = vn)) (PreH23 : (list_within_bound UINT_MOD l1 )) (PreH24 : (list_within_bound UINT_MOD l2 )) (PreH25 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH26 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH27 : ((last (l1) (1)) >= 1)) (PreH28 : ((last (l2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "t" ) )) # Ptr  |-> retval)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (un + vn )) ”
.

Definition mpz_mul_safety_wit_21 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (rcap >= 0)) (PreH20 : (rcap <= INT_MAX)) (PreH21 : ((Zlength (l1)) = un)) (PreH22 : ((Zlength (l2)) = vn)) (PreH23 : (list_within_bound UINT_MOD l1 )) (PreH24 : (list_within_bound UINT_MOD l2 )) (PreH25 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH26 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH27 : ((last (l1) (1)) >= 1)) (PreH28 : ((last (l2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "t" ) )) # Ptr  |-> retval)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_mul_safety_wit_22 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (un + vn ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH5 : (un >= vn)) (PreH6 : (rn = (un + vn ))) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((un + vn ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
|--
  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (un + vn )) ”
.

Definition mpz_mul_safety_wit_23 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (vn + un ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH5 : (rn = (un + vn ))) (PreH6 : (un < vn)) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((vn + un ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
|--
  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (un + vn )) ”
.

Definition mpz_mul_safety_wit_24 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (un + vn ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH5 : (un >= vn)) (PreH6 : (rn = (un + vn ))) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((un + vn ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
|--
  “ (((un + vn ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((un + vn ) - 1 )) ”
.

Definition mpz_mul_safety_wit_25 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (un + vn ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH5 : (un >= vn)) (PreH6 : (rn = (un + vn ))) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((un + vn ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_safety_wit_26 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (vn + un ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH5 : (rn = (un + vn ))) (PreH6 : (un < vn)) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((vn + un ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
|--
  “ (((un + vn ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((un + vn ) - 1 )) ”
.

Definition mpz_mul_safety_wit_27 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (vn + un ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH5 : (rn = (un + vn ))) (PreH6 : (un < vn)) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((vn + un ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_safety_wit_28 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (un + vn ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH5 : (un >= vn)) (PreH6 : (rn = (un + vn ))) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((un + vn ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_29 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (vn + un ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH5 : (rn = (un + vn ))) (PreH6 : (un < vn)) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((vn + un ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_safety_wit_30 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (((un + vn ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((un + vn ) - 1 )) ”
.

Definition mpz_mul_safety_wit_31 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_safety_wit_32 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (((un + vn ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((un + vn ) - 1 )) ”
.

Definition mpz_mul_safety_wit_33 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_safety_wit_34 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> ((un + vn ) - 1 ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (((un + vn ) - 1 ) <> (INT_MIN)) ”
.

Definition mpz_mul_safety_wit_35 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> ((un + vn ) - 1 ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ (((un + vn ) - 1 ) <> (INT_MIN)) ”
.

Definition mpz_mul_safety_wit_36 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ ((un + vn ) <> (INT_MIN)) ”
.

Definition mpz_mul_safety_wit_37 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  “ ((un + vn ) <> (INT_MIN)) ”
.

Definition mpz_mul_entail_wit_1_1 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 > 0)) (PreH4 : (size < 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (size <> 0)) (PreH7 : (same_sign z2 size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign z1 size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  EX (op2cap: Z)  (op2ptr: Z)  (op1cap: Z)  (op1ptr: Z)  (rptr: Z)  (l2: (@list Z))  (l1: (@list Z))  (rcap: Z)  (rsize: Z)  (op1size: Z)  (op2size: Z) ,
  “ ((retval + retval_2 ) = (retval + retval_2 )) ” 
  &&  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (mpz_mul_sign 1 op1size op2size ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (op1size))) ” 
  &&  “ (retval_2 = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr retval l1 )
  **  (UIntArray.undef_seg op1ptr retval op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr retval_2 l2 )
  **  (UIntArray.undef_seg op2ptr retval_2 op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size_2 > 0)) (PreH6 : (size < 0)) (PreH7 : (size_2 <> 0)) (PreH8 : (size <> 0)) (PreH9 : (same_sign z2 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap_2)) (PreH11 : (same_sign z1 size )) (PreH12 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (mpz_mul_sign 1 size size_2 ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ (same_sign old size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (cap_3 >= 0) ” 
  &&  “ (cap_3 <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  (UIntArray.full ptr retval l1 )
  **  (UIntArray.full ptr_2 retval_2 l2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
).

Definition mpz_mul_entail_wit_1_2 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 < 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  EX (op2cap: Z)  (op2ptr: Z)  (op1cap: Z)  (op1ptr: Z)  (rptr: Z)  (l2: (@list Z))  (l1: (@list Z))  (rcap: Z)  (rsize: Z)  (op1size: Z)  (op2size: Z) ,
  “ ((retval + retval_2 ) = (retval + retval_2 )) ” 
  &&  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (mpz_mul_sign 1 op1size op2size ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (op1size))) ” 
  &&  “ (retval_2 = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr retval l1 )
  **  (UIntArray.undef_seg op1ptr retval op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr retval_2 l2 )
  **  (UIntArray.undef_seg op2ptr retval_2 op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size_2 < 0)) (PreH6 : (size > 0)) (PreH7 : (size >= 0)) (PreH8 : (size_2 <> 0)) (PreH9 : (size <> 0)) (PreH10 : (same_sign z2 size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)) (PreH12 : (same_sign z1 size )) (PreH13 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (mpz_mul_sign 1 size size_2 ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ (same_sign old size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (cap_3 >= 0) ” 
  &&  “ (cap_3 <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  (UIntArray.full ptr retval l1 )
  **  (UIntArray.full ptr_2 retval_2 l2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
).

Definition mpz_mul_entail_wit_1_3 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size_2 >= 0)) (PreH4 : (size > 0)) (PreH5 : (size >= 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  EX (op2cap: Z)  (op2ptr: Z)  (op1cap: Z)  (op1ptr: Z)  (rptr: Z)  (l2: (@list Z))  (l1: (@list Z))  (rcap: Z)  (rsize: Z)  (op1size: Z)  (op2size: Z) ,
  “ ((retval + retval_2 ) = (retval + retval_2 )) ” 
  &&  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (mpz_mul_sign 0 op1size op2size ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (op1size))) ” 
  &&  “ (retval_2 = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr retval l1 )
  **  (UIntArray.undef_seg op1ptr retval op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr retval_2 l2 )
  **  (UIntArray.undef_seg op2ptr retval_2 op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size_2 >= 0)) (PreH6 : (size > 0)) (PreH7 : (size >= 0)) (PreH8 : (size_2 <> 0)) (PreH9 : (size <> 0)) (PreH10 : (same_sign z2 size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)) (PreH12 : (same_sign z1 size )) (PreH13 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (mpz_mul_sign 0 size size_2 ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ (same_sign old size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (cap_3 >= 0) ” 
  &&  “ (cap_3 <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  (UIntArray.full ptr retval l1 )
  **  (UIntArray.full ptr_2 retval_2 l2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
).

Definition mpz_mul_entail_wit_1_4 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <= 0)) (PreH4 : (size_2 <= 0)) (PreH5 : (size < 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (size <> 0)) (PreH8 : (same_sign z2 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (same_sign z1 size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  EX (op2cap: Z)  (op2ptr: Z)  (op1cap: Z)  (op1ptr: Z)  (rptr: Z)  (l2: (@list Z))  (l1: (@list Z))  (rcap: Z)  (rsize: Z)  (op1size: Z)  (op2size: Z) ,
  “ ((retval + retval_2 ) = (retval + retval_2 )) ” 
  &&  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (mpz_mul_sign 0 op1size op2size ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (op1size))) ” 
  &&  “ (retval_2 = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr retval l1 )
  **  (UIntArray.undef_seg op1ptr retval op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr retval_2 l2 )
  **  (UIntArray.undef_seg op2ptr retval_2 op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval: Z) (retval_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <= 0)) (PreH6 : (size_2 <= 0)) (PreH7 : (size < 0)) (PreH8 : (size_2 <> 0)) (PreH9 : (size <> 0)) (PreH10 : (same_sign z2 size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)) (PreH12 : (same_sign z1 size )) (PreH13 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ (retval > 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (mpz_mul_sign 0 size size_2 ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ (same_sign old size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (cap_3 >= 0) ” 
  &&  “ (cap_3 <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = retval) ” 
  &&  “ ((Zlength (l2)) = retval_2) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  (UIntArray.full ptr retval l1 )
  **  (UIntArray.full ptr_2 retval_2 l2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
).

Definition mpz_mul_entail_wit_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr_2: Z) (rsize_2: Z) (rcap_2: Z) (op1ptr: Z) (op1size_2: Z) (op1cap_2: Z) (op2ptr: Z) (op2size_2: Z) (op2cap_2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (x_callee__mp_size: Z) (ptr: Z) (PreH1 : (ptr <> 0)) (PreH2 : (x_callee__mp_size = 0)) (PreH3 : (retval <> 0)) (PreH4 : (rn = (un + vn ))) (PreH5 : (un > 0)) (PreH6 : (vn > 0)) (PreH7 : (0 <= sign)) (PreH8 : (sign <= 1)) (PreH9 : (mpz_mul_sign sign op1size_2 op2size_2 )) (PreH10 : (un <= INT_MAX)) (PreH11 : (vn <= INT_MAX)) (PreH12 : ((un + vn ) <= INT_MAX)) (PreH13 : (un = (Zabs (op1size_2)))) (PreH14 : (vn = (Zabs (op2size_2)))) (PreH15 : (op1size_2 <> 0)) (PreH16 : (op2size_2 <> 0)) (PreH17 : (same_sign z1 op1size_2 )) (PreH18 : (same_sign z2 op2size_2 )) (PreH19 : (same_sign old rsize_2 )) (PreH20 : ((Zabs (rsize_2)) <= rcap_2)) (PreH21 : (rcap_2 >= 0)) (PreH22 : (rcap_2 <= INT_MAX)) (PreH23 : ((Zlength (l1_2)) = un)) (PreH24 : ((Zlength (l2_2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1_2 )) (PreH26 : (list_within_bound UINT_MOD l2_2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1_2)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2_2)) = (Zabs (z2)))) (PreH29 : ((last (l1_2) (1)) >= 1)) (PreH30 : ((last (l2_2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (un + vn ))
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> x_callee__mp_size)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr (un + vn ) )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap_2)
  **  (UIntArray.full op1ptr un l1_2 )
  **  (UIntArray.undef_seg op1ptr un op1cap_2 )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap_2)
  **  (UIntArray.full op2ptr vn l2_2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap_2 )
  **  (mpd_store_Z_compact UINT_MOD rptr_2 (Zabs (old)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg rptr_2 (Zabs (rsize_2)) rcap_2 )
|--
  EX (op2cap: Z)  (op1cap: Z)  (t__mp_d: Z)  (t__mp_alloc: Z)  (t__mp_size: Z)  (rptr: Z)  (l2: (@list Z))  (l1: (@list Z))  (rcap: Z)  (rsize: Z)  (op1size: Z)  (op2size: Z) ,
  “ (rn = (un + vn )) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (t__mp_size = 0) ” 
  &&  “ (t__mp_alloc = (un + vn )) ” 
  &&  “ (t__mp_d = ptr) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (UIntArray.undef_full ptr (un + vn ) )
.

Definition mpz_mul_entail_wit_3 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr_2: Z) (rsize_2: Z) (rcap_2: Z) (op1ptr: Z) (op1size_2: Z) (op1cap_2: Z) (op2ptr: Z) (op2size_2: Z) (op2cap_2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size_2: Z) (t__mp_alloc_2: Z) (t__mp_d_2: Z) (rp: Z) (PreH1 : (un < vn)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size_2 op2size_2 )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size_2)))) (PreH12 : (vn = (Zabs (op2size_2)))) (PreH13 : (op1size_2 <> 0)) (PreH14 : (op2size_2 <> 0)) (PreH15 : (same_sign z1 op1size_2 )) (PreH16 : (same_sign z2 op2size_2 )) (PreH17 : (same_sign old rsize_2 )) (PreH18 : ((Zabs (rsize_2)) <= rcap_2)) (PreH19 : ((Zlength (l1_2)) = un)) (PreH20 : ((Zlength (l2_2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1_2 )) (PreH22 : (list_within_bound UINT_MOD l2_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1_2)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2_2)) = (Zabs (z2)))) (PreH25 : ((last (l1_2) (1)) >= 1)) (PreH26 : ((last (l2_2) (1)) >= 1)) (PreH27 : (t__mp_size_2 = 0)) (PreH28 : (t__mp_alloc_2 = (un + vn ))) (PreH29 : (t__mp_d_2 = rp)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap_2)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr_2)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size_2)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc_2)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD rptr_2 (Zabs (old)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg rptr_2 (Zabs (rsize_2)) rcap_2 )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap_2)
  **  (UIntArray.full op1ptr un l1_2 )
  **  (UIntArray.undef_seg op1ptr un op1cap_2 )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap_2)
  **  (UIntArray.full op2ptr vn l2_2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap_2 )
  **  (UIntArray.undef_full rp (un + vn ) )
|--
  EX (op2cap: Z)  (op1cap: Z)  (t__mp_d: Z)  (t__mp_alloc: Z)  (t__mp_size: Z)  (rptr: Z)  (l2: (@list Z))  (l1: (@list Z))  (rcap: Z)  (rsize: Z)  (op1size: Z)  (op2size: Z) ,
  “ (rn = (un + vn )) ” 
  &&  “ (un < vn) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((vn + un ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (t__mp_size = 0) ” 
  &&  “ (t__mp_alloc = (un + vn )) ” 
  &&  “ (t__mp_d = rp) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (UIntArray.undef_full rp (vn + un ) )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rptr_2: Z) (rsize_2: Z) (rcap_2: Z) (op1size_2: Z) (op2size_2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size_2: Z) (t__mp_alloc_2: Z) (t__mp_d_2: Z) (rp: Z) (PreH1 : (un < vn)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size_2 op2size_2 )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size_2)))) (PreH12 : (vn = (Zabs (op2size_2)))) (PreH13 : (op1size_2 <> 0)) (PreH14 : (op2size_2 <> 0)) (PreH15 : (same_sign z1 op1size_2 )) (PreH16 : (same_sign z2 op2size_2 )) (PreH17 : (same_sign old rsize_2 )) (PreH18 : ((Zabs (rsize_2)) <= rcap_2)) (PreH19 : ((Zlength (l1_2)) = un)) (PreH20 : ((Zlength (l2_2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1_2 )) (PreH22 : (list_within_bound UINT_MOD l2_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1_2)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2_2)) = (Zabs (z2)))) (PreH25 : ((last (l1_2) (1)) >= 1)) (PreH26 : ((last (l2_2) (1)) >= 1)) (PreH27 : (t__mp_size_2 = 0)) (PreH28 : (t__mp_alloc_2 = (un + vn ))) (PreH29 : (t__mp_d_2 = rp)) ,
  (mpd_store_Z_compact UINT_MOD rptr_2 (Zabs (old)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_full rp (un + vn ) )
|--
  (mpd_store_Z_compact UINT_MOD rptr_2 (Zabs (old)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_full rp (vn + un ) )
).

Definition mpz_mul_entail_wit_3_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rptr_2: Z) (rsize_2: Z) (rcap_2: Z) (op1size_2: Z) (op2size_2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size_2: Z) (t__mp_alloc_2: Z) (t__mp_d_2: Z) (rp: Z) (PreH1 : (un < vn)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size_2 op2size_2 )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size_2)))) (PreH12 : (vn = (Zabs (op2size_2)))) (PreH13 : (op1size_2 <> 0)) (PreH14 : (op2size_2 <> 0)) (PreH15 : (same_sign z1 op1size_2 )) (PreH16 : (same_sign z2 op2size_2 )) (PreH17 : (same_sign old rsize_2 )) (PreH18 : ((Zabs (rsize_2)) <= rcap_2)) (PreH19 : ((Zlength (l1_2)) = un)) (PreH20 : ((Zlength (l2_2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1_2 )) (PreH22 : (list_within_bound UINT_MOD l2_2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1_2)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2_2)) = (Zabs (z2)))) (PreH25 : ((last (l1_2) (1)) >= 1)) (PreH26 : ((last (l2_2) (1)) >= 1)) (PreH27 : (t__mp_size_2 = 0)) (PreH28 : (t__mp_alloc_2 = (un + vn ))) (PreH29 : (t__mp_d_2 = rp)) ,
  (mpd_store_Z_compact UINT_MOD rptr_2 (Zabs (old)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_full rp (un + vn ) )
|--
  (mpd_store_Z_compact UINT_MOD rptr_2 (Zabs (old)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_full rp (vn + un ) )
.

Definition mpz_mul_entail_wit_4_1 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rn" ) )) # Int  |-> (-((un + vn ) - 1 )))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-((un + vn ) - 1 )))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs ((-((un + vn ) - 1 )))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) (-((un + vn ) - 1 )) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs ((-((un + vn ) - 1 )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-((un + vn ) - 1 )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_1_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_1_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_1_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs ((-((un + vn ) - 1 )))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_1_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) (-((un + vn ) - 1 )) ) ”
.

Definition mpz_mul_entail_wit_4_1_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs ((-((un + vn ) - 1 )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-((un + vn ) - 1 )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_2 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rn" ) )) # Int  |-> (-((un + vn ) - 1 )))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-((un + vn ) - 1 )))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs ((-((un + vn ) - 1 )))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) (-((un + vn ) - 1 )) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs ((-((un + vn ) - 1 )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-((un + vn ) - 1 )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_2_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_2_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_2_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs ((-((un + vn ) - 1 )))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_2_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) (-((un + vn ) - 1 )) ) ”
.

Definition mpz_mul_entail_wit_4_2_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs ((-((un + vn ) - 1 )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-((un + vn ) - 1 )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_3 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rn" ) )) # Int  |-> (-(un + vn )))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-(un + vn )))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs ((-(un + vn )))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) (-(un + vn )) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs ((-(un + vn )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-(un + vn )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_3_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_3_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_3_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs ((-(un + vn )))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_3_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) (-(un + vn )) ) ”
.

Definition mpz_mul_entail_wit_4_3_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs ((-(un + vn )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-(un + vn )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_4 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rn" ) )) # Int  |-> (-(un + vn )))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-(un + vn )))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs ((-(un + vn )))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) (-(un + vn )) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs ((-(un + vn )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-(un + vn )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_4_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_4_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_4_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs ((-(un + vn )))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_4_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) (-(un + vn )) ) ”
.

Definition mpz_mul_entail_wit_4_4_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign <> 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs ((-(un + vn )))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((-(un + vn )))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_5 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rn" ) )) # Int  |-> ((un + vn ) - 1 ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> ((un + vn ) - 1 ))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs (((un + vn ) - 1 ))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) ((un + vn ) - 1 ) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs (((un + vn ) - 1 ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs (((un + vn ) - 1 ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_5_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_5_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_5_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (((un + vn ) - 1 ))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_5_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) ((un + vn ) - 1 ) ) ”
.

Definition mpz_mul_entail_wit_4_5_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs (((un + vn ) - 1 ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs (((un + vn ) - 1 ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_6 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rn" ) )) # Int  |-> ((un + vn ) - 1 ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> ((un + vn ) - 1 ))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs (((un + vn ) - 1 ))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) ((un + vn ) - 1 ) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs (((un + vn ) - 1 ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs (((un + vn ) - 1 ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_6_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_6_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_6_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (((un + vn ) - 1 ))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_6_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) ((un + vn ) - 1 ) ) ”
.

Definition mpz_mul_entail_wit_4_6_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs (((un + vn ) - 1 ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs (((un + vn ) - 1 ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_7 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (un + vn ))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs ((un + vn ))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) (un + vn ) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs ((un + vn ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((un + vn ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_7_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_7_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_7_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs ((un + vn ))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_7_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) (un + vn ) ) ”
.

Definition mpz_mul_entail_wit_4_7_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (un + vn ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH6 : (un >= vn)) (PreH7 : (rn = (un + vn ))) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((un + vn ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs ((un + vn ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((un + vn ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_entail_wit_4_8 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((( &( "rn" ) )) # Int  |-> (un + vn ))
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (un + vn ))
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
  **  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ” 
  &&  “ ((Zabs (op2size)) <= op2cap) ” 
  &&  “ ((Zabs ((un + vn ))) <= t__mp_alloc) ” 
  &&  “ (same_sign (z1 * z2 ) (un + vn ) ) ”
  &&  (UIntArray.undef_seg t__mp_d (Zabs ((un + vn ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((un + vn ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
).

Definition mpz_mul_entail_wit_4_8_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op1size)) <= op1cap) ”
.

Definition mpz_mul_entail_wit_4_8_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs (op2size)) <= op2cap) ”
.

Definition mpz_mul_entail_wit_4_8_split_goal_3 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ ((Zabs ((un + vn ))) <= t__mp_alloc) ”
.

Definition mpz_mul_entail_wit_4_8_split_goal_4 := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  “ (same_sign (z1 * z2 ) (un + vn ) ) ”
.

Definition mpz_mul_entail_wit_4_8_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op2ptr: Z) (op2size: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Znth ((un + vn ) - 1 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = (vn + un ))) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH5 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH6 : (rn = (un + vn ))) (PreH7 : (un < vn)) (PreH8 : (un > 0)) (PreH9 : (vn > 0)) (PreH10 : (0 <= sign)) (PreH11 : (sign <= 1)) (PreH12 : (mpz_mul_sign sign op1size op2size )) (PreH13 : (un <= INT_MAX)) (PreH14 : (vn <= INT_MAX)) (PreH15 : ((vn + un ) <= INT_MAX)) (PreH16 : (un = (Zabs (op1size)))) (PreH17 : (vn = (Zabs (op2size)))) (PreH18 : (op1size <> 0)) (PreH19 : (op2size <> 0)) (PreH20 : (same_sign z1 op1size )) (PreH21 : (same_sign z2 op2size )) (PreH22 : (same_sign old rsize )) (PreH23 : ((Zabs (rsize)) <= rcap)) (PreH24 : ((Zlength (l1)) = un)) (PreH25 : ((Zlength (l2)) = vn)) (PreH26 : (list_within_bound UINT_MOD l1 )) (PreH27 : (list_within_bound UINT_MOD l2 )) (PreH28 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH29 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH30 : ((last (l1) (1)) >= 1)) (PreH31 : ((last (l2) (1)) >= 1)) (PreH32 : (t__mp_size = 0)) (PreH33 : (t__mp_alloc = (un + vn ))) (PreH34 : (t__mp_d = rp)) (PreH35 : (sign = 0)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
|--
  (UIntArray.undef_seg t__mp_d (Zabs ((un + vn ))) t__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD t__mp_d (Zabs ((z1 * z2 ))) (Zabs ((un + vn ))) )
  **  (mpd_store_Z_compact UINT_MOD op2ptr (Zabs (z2)) (Zabs (op2size)) )
  **  (mpd_store_Z_compact UINT_MOD op1ptr (Zabs (z1)) (Zabs (op1size)) )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
.

Definition mpz_mul_return_wit_1 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size = 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_3)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size = 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  “ ((Zabs (0)) <= cap_3) ” 
  &&  “ (same_sign (z1 * z2 ) 0 ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr_3 (Zabs (0)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs ((z1 * z2 ))) (Zabs (0)) )
).

Definition mpz_mul_return_wit_1_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size = 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  “ ((Zabs (0)) <= cap_3) ”
.

Definition mpz_mul_return_wit_1_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size = 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  “ (same_sign (z1 * z2 ) 0 ) ”
.

Definition mpz_mul_return_wit_1_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size = 0)) (PreH4 : (same_sign z2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign z1 size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr_3 (Zabs (0)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs ((z1 * z2 ))) (Zabs (0)) )
.

Definition mpz_mul_return_wit_2 := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size_2 = 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_3)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
) \/
(
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size_2 = 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  “ ((Zabs (0)) <= cap_3) ” 
  &&  “ (same_sign (z1 * z2 ) 0 ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr_3 (Zabs (0)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs ((z1 * z2 ))) (Zabs (0)) )
).

Definition mpz_mul_return_wit_2_split_goal_1 := 
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size_2 = 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  “ ((Zabs (0)) <= cap_3) ”
.

Definition mpz_mul_return_wit_2_split_goal_2 := 
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size_2 = 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  “ (same_sign (z1 * z2 ) 0 ) ”
.

Definition mpz_mul_return_wit_2_split_goal_spatial := 
forall (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign old size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (size_2 = 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr_3 (Zabs (0)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs ((z1 * z2 ))) (Zabs (0)) )
.

Definition mpz_mul_return_wit_3 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) ,
  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_mul_partial_solve_wit_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) ,
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
  **  (store_Z op2_pre z2 )
.

Definition mpz_mul_partial_solve_wit_2 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign z1 size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
  **  (store_Z op2_pre z2 )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_3 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign z2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign z1 size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr_3: Z) ,
  “ (same_sign old size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (size = 0) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_3)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_mul_partial_solve_wit_4 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (size <> 0)) (PreH3 : (same_sign z2 size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (same_sign z1 size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr_3: Z) ,
  “ (same_sign old size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (size_2 = 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_3 (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (old)) (Zabs (size_3)) )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_3)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_mul_partial_solve_wit_5_pure := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 > 0)) (PreH2 : (size < 0)) (PreH3 : (size_2 <> 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size_2 <= INT_MAX)) (PreH6 : (1 >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (size_2 > 0)) (PreH12 : (size < 0)) (PreH13 : (size_2 <> 0)) (PreH14 : (size <> 0)) (PreH15 : (same_sign z2 size_2 )) (PreH16 : ((Zabs (size_2)) <= cap_2)) (PreH17 : (same_sign z1 size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_mul_partial_solve_wit_5_pure_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size_2 <= INT_MAX)) (PreH6 : (1 >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (size_2 > 0)) (PreH12 : (size < 0)) (PreH13 : (size_2 <> 0)) (PreH14 : (size <> 0)) (PreH15 : (same_sign z2 size_2 )) (PreH16 : ((Zabs (size_2)) <= cap_2)) (PreH17 : (same_sign z1 size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_mul_partial_solve_wit_5_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 > 0)) (PreH2 : (size < 0)) (PreH3 : (size_2 <> 0)) (PreH4 : (size <> 0)) (PreH5 : (same_sign z2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign z1 size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (size_2 > 0) ” 
  &&  “ (size < 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_5 := mpz_mul_partial_solve_wit_5_pure -> mpz_mul_partial_solve_wit_5_aux.

Definition mpz_mul_partial_solve_wit_6_pure := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 < 0)) (PreH2 : (size > 0)) (PreH3 : (size >= 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ”
.

Definition mpz_mul_partial_solve_wit_6_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 < 0)) (PreH2 : (size > 0)) (PreH3 : (size >= 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (size_2 < 0) ” 
  &&  “ (size > 0) ” 
  &&  “ (size >= 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_6 := mpz_mul_partial_solve_wit_6_pure -> mpz_mul_partial_solve_wit_6_aux.

Definition mpz_mul_partial_solve_wit_7_pure := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 >= 0)) (PreH2 : (size > 0)) (PreH3 : (size >= 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ”
.

Definition mpz_mul_partial_solve_wit_7_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 >= 0)) (PreH2 : (size > 0)) (PreH3 : (size >= 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (size_2 >= 0) ” 
  &&  “ (size > 0) ” 
  &&  “ (size >= 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_7 := mpz_mul_partial_solve_wit_7_pure -> mpz_mul_partial_solve_wit_7_aux.

Definition mpz_mul_partial_solve_wit_8_pure := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size <= 0)) (PreH2 : (size_2 <= 0)) (PreH3 : (size < 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size_2 <= INT_MAX)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (size <= 0)) (PreH12 : (size_2 <= 0)) (PreH13 : (size < 0)) (PreH14 : (size_2 <> 0)) (PreH15 : (size <> 0)) (PreH16 : (same_sign z2 size_2 )) (PreH17 : ((Zabs (size_2)) <= cap_2)) (PreH18 : (same_sign z1 size )) (PreH19 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_mul_partial_solve_wit_8_pure_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size_2 <= INT_MAX)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (size <= 0)) (PreH12 : (size_2 <= 0)) (PreH13 : (size < 0)) (PreH14 : (size_2 <> 0)) (PreH15 : (size <> 0)) (PreH16 : (same_sign z2 size_2 )) (PreH17 : ((Zabs (size_2)) <= cap_2)) (PreH18 : (same_sign z1 size )) (PreH19 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size_2)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_mul_partial_solve_wit_8_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size <= 0)) (PreH2 : (size_2 <= 0)) (PreH3 : (size < 0)) (PreH4 : (size_2 <> 0)) (PreH5 : (size <> 0)) (PreH6 : (same_sign z2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign z1 size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (size <= 0) ” 
  &&  “ (size_2 <= 0) ” 
  &&  “ (size < 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign z2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z1 size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size_2)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_8 := mpz_mul_partial_solve_wit_8_pure -> mpz_mul_partial_solve_wit_8_aux.

Definition mpz_mul_partial_solve_wit_9_pure := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size > 0)) (PreH3 : (size_2 < 0)) (PreH4 : (size <> 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (same_sign z2 size )) (PreH7 : ((Zabs (size)) <= cap_2)) (PreH8 : (same_sign z1 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ”
.

Definition mpz_mul_partial_solve_wit_9_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size > 0)) (PreH3 : (size_2 < 0)) (PreH4 : (size <> 0)) (PreH5 : (size_2 <> 0)) (PreH6 : (same_sign z2 size )) (PreH7 : ((Zabs (size)) <= cap_2)) (PreH8 : (same_sign z1 size_2 )) (PreH9 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (size > 0) ” 
  &&  “ (size_2 < 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z2 size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (same_sign z1 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_9 := mpz_mul_partial_solve_wit_9_pure -> mpz_mul_partial_solve_wit_9_aux.

Definition mpz_mul_partial_solve_wit_10_pure := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size < 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 >= 0)) (PreH5 : (size <> 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (same_sign z2 size )) (PreH8 : ((Zabs (size)) <= cap_2)) (PreH9 : (same_sign z1 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size <= INT_MAX)) (PreH7 : (1 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (size < 0)) (PreH15 : (size_2 > 0)) (PreH16 : (size_2 >= 0)) (PreH17 : (size <> 0)) (PreH18 : (size_2 <> 0)) (PreH19 : (same_sign z2 size )) (PreH20 : ((Zabs (size)) <= cap_2)) (PreH21 : (same_sign z1 size_2 )) (PreH22 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_mul_partial_solve_wit_10_pure_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size <= INT_MAX)) (PreH7 : (1 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (size < 0)) (PreH15 : (size_2 > 0)) (PreH16 : (size_2 >= 0)) (PreH17 : (size <> 0)) (PreH18 : (size_2 <> 0)) (PreH19 : (same_sign z2 size )) (PreH20 : ((Zabs (size)) <= cap_2)) (PreH21 : (same_sign z1 size_2 )) (PreH22 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 1)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_mul_partial_solve_wit_10_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size < 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 >= 0)) (PreH5 : (size <> 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (same_sign z2 size )) (PreH8 : ((Zabs (size)) <= cap_2)) (PreH9 : (same_sign z1 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (size < 0) ” 
  &&  “ (size_2 > 0) ” 
  &&  “ (size_2 >= 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z2 size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (same_sign z1 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_10 := mpz_mul_partial_solve_wit_10_pure -> mpz_mul_partial_solve_wit_10_aux.

Definition mpz_mul_partial_solve_wit_11_pure := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size >= 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 >= 0)) (PreH5 : (size <> 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (same_sign z2 size )) (PreH8 : ((Zabs (size)) <= cap_2)) (PreH9 : (same_sign z1 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ”
.

Definition mpz_mul_partial_solve_wit_11_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size >= 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 >= 0)) (PreH5 : (size <> 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (same_sign z2 size )) (PreH8 : ((Zabs (size)) <= cap_2)) (PreH9 : (same_sign z1 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (size >= 0) ” 
  &&  “ (size_2 > 0) ” 
  &&  “ (size_2 >= 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z2 size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (same_sign z1 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_11 := mpz_mul_partial_solve_wit_11_pure -> mpz_mul_partial_solve_wit_11_aux.

Definition mpz_mul_partial_solve_wit_12_pure := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size_2 <= 0)) (PreH3 : (size <= 0)) (PreH4 : (size_2 < 0)) (PreH5 : (size <> 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (same_sign z2 size )) (PreH8 : ((Zabs (size)) <= cap_2)) (PreH9 : (same_sign z1 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (size_2 <= 0)) (PreH15 : (size <= 0)) (PreH16 : (size_2 < 0)) (PreH17 : (size <> 0)) (PreH18 : (size_2 <> 0)) (PreH19 : (same_sign z2 size )) (PreH20 : ((Zabs (size)) <= cap_2)) (PreH21 : (same_sign z1 size_2 )) (PreH22 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_mul_partial_solve_wit_12_pure_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (size_2 <= 0)) (PreH15 : (size <= 0)) (PreH16 : (size_2 < 0)) (PreH17 : (size <> 0)) (PreH18 : (size_2 <> 0)) (PreH19 : (same_sign z2 size )) (PreH20 : ((Zabs (size)) <= cap_2)) (PreH21 : (same_sign z1 size_2 )) (PreH22 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "vn" ) )) # Int  |-> size)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "sign" ) )) # Int  |-> 0)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_mul_partial_solve_wit_12_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (ptr: Z) (size_2: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (size_2)))) (PreH2 : (size_2 <= 0)) (PreH3 : (size <= 0)) (PreH4 : (size_2 < 0)) (PreH5 : (size <> 0)) (PreH6 : (size_2 <> 0)) (PreH7 : (same_sign z2 size )) (PreH8 : ((Zabs (size)) <= cap_2)) (PreH9 : (same_sign z1 size_2 )) (PreH10 : ((Zabs (size_2)) <= cap)) ,
  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (size_2 <= 0) ” 
  &&  “ (size <= 0) ” 
  &&  “ (size_2 < 0) ” 
  &&  “ (size <> 0) ” 
  &&  “ (size_2 <> 0) ” 
  &&  “ (same_sign z2 size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (same_sign z1 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z2)) (Zabs (size)) )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z1)) (Zabs (size_2)) )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z rop_pre old )
.

Definition mpz_mul_partial_solve_wit_12 := mpz_mul_partial_solve_wit_12_pure -> mpz_mul_partial_solve_wit_12_aux.

Definition mpz_mul_partial_solve_wit_13 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (PreH1 : (rn = (un + vn ))) (PreH2 : (un > 0)) (PreH3 : (vn > 0)) (PreH4 : (0 <= sign)) (PreH5 : (sign <= 1)) (PreH6 : (mpz_mul_sign sign op1size op2size )) (PreH7 : (un <= INT_MAX)) (PreH8 : (vn <= INT_MAX)) (PreH9 : ((un + vn ) <= INT_MAX)) (PreH10 : (un = (Zabs (op1size)))) (PreH11 : (vn = (Zabs (op2size)))) (PreH12 : (op1size <> 0)) (PreH13 : (op2size <> 0)) (PreH14 : (same_sign z1 op1size )) (PreH15 : (same_sign z2 op2size )) (PreH16 : (same_sign old rsize )) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (rcap >= 0)) (PreH19 : (rcap <= INT_MAX)) (PreH20 : ((Zlength (l1)) = un)) (PreH21 : ((Zlength (l2)) = vn)) (PreH22 : (list_within_bound UINT_MOD l1 )) (PreH23 : (list_within_bound UINT_MOD l2 )) (PreH24 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH25 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH26 : ((last (l1) (1)) >= 1)) (PreH27 : ((last (l2) (1)) >= 1)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ (rn = (un + vn )) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
.

Definition mpz_mul_partial_solve_wit_14_pure := 
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (rcap >= 0)) (PreH20 : (rcap <= INT_MAX)) (PreH21 : ((Zlength (l1)) = un)) (PreH22 : ((Zlength (l2)) = vn)) (PreH23 : (list_within_bound UINT_MOD l1 )) (PreH24 : (list_within_bound UINT_MOD l2 )) (PreH25 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH26 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH27 : ((last (l1) (1)) >= 1)) (PreH28 : ((last (l2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "t" ) )) # Ptr  |-> retval)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ ((un + vn ) > 0) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((un + vn )) (64)) * 32 )) (64)) = ((un + vn ) * 32 )) ”
) \/
(
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (PreH1 : (op2cap <= INT_MAX)) (PreH2 : (op2size <= INT_MAX)) (PreH3 : (op1cap <= INT_MAX)) (PreH4 : (op1size <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (sign <= INT_MAX)) (PreH7 : (rn <= INT_MAX)) (PreH8 : (op2cap >= INT_MIN)) (PreH9 : (op2size >= INT_MIN)) (PreH10 : (op1cap >= INT_MIN)) (PreH11 : (op1size >= INT_MIN)) (PreH12 : (rcap >= INT_MIN)) (PreH13 : (rsize >= INT_MIN)) (PreH14 : (sign >= INT_MIN)) (PreH15 : (vn >= INT_MIN)) (PreH16 : (un >= INT_MIN)) (PreH17 : (rn >= INT_MIN)) (PreH18 : (retval <> 0)) (PreH19 : (rn = (un + vn ))) (PreH20 : (un > 0)) (PreH21 : (vn > 0)) (PreH22 : (0 <= sign)) (PreH23 : (sign <= 1)) (PreH24 : (mpz_mul_sign sign op1size op2size )) (PreH25 : (un <= INT_MAX)) (PreH26 : (vn <= INT_MAX)) (PreH27 : ((un + vn ) <= INT_MAX)) (PreH28 : (un = (Zabs (op1size)))) (PreH29 : (vn = (Zabs (op2size)))) (PreH30 : (op1size <> 0)) (PreH31 : (op2size <> 0)) (PreH32 : (same_sign z1 op1size )) (PreH33 : (same_sign z2 op2size )) (PreH34 : (same_sign old rsize )) (PreH35 : ((Zabs (rsize)) <= rcap)) (PreH36 : (rcap >= 0)) (PreH37 : (rcap <= INT_MAX)) (PreH38 : ((Zlength (l1)) = un)) (PreH39 : ((Zlength (l2)) = vn)) (PreH40 : (list_within_bound UINT_MOD l1 )) (PreH41 : (list_within_bound UINT_MOD l2 )) (PreH42 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH43 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH44 : ((last (l1) (1)) >= 1)) (PreH45 : ((last (l2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "t" ) )) # Ptr  |-> retval)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits ((un + vn )) (64)) * 32 )) (64)) = ((un + vn ) * 32 )) ”
).

Definition mpz_mul_partial_solve_wit_14_pure_split_goal_1 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (PreH1 : (op2cap <= INT_MAX)) (PreH2 : (op2size <= INT_MAX)) (PreH3 : (op1cap <= INT_MAX)) (PreH4 : (op1size <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (sign <= INT_MAX)) (PreH7 : (rn <= INT_MAX)) (PreH8 : (op2cap >= INT_MIN)) (PreH9 : (op2size >= INT_MIN)) (PreH10 : (op1cap >= INT_MIN)) (PreH11 : (op1size >= INT_MIN)) (PreH12 : (rcap >= INT_MIN)) (PreH13 : (rsize >= INT_MIN)) (PreH14 : (sign >= INT_MIN)) (PreH15 : (vn >= INT_MIN)) (PreH16 : (un >= INT_MIN)) (PreH17 : (rn >= INT_MIN)) (PreH18 : (retval <> 0)) (PreH19 : (rn = (un + vn ))) (PreH20 : (un > 0)) (PreH21 : (vn > 0)) (PreH22 : (0 <= sign)) (PreH23 : (sign <= 1)) (PreH24 : (mpz_mul_sign sign op1size op2size )) (PreH25 : (un <= INT_MAX)) (PreH26 : (vn <= INT_MAX)) (PreH27 : ((un + vn ) <= INT_MAX)) (PreH28 : (un = (Zabs (op1size)))) (PreH29 : (vn = (Zabs (op2size)))) (PreH30 : (op1size <> 0)) (PreH31 : (op2size <> 0)) (PreH32 : (same_sign z1 op1size )) (PreH33 : (same_sign z2 op2size )) (PreH34 : (same_sign old rsize )) (PreH35 : ((Zabs (rsize)) <= rcap)) (PreH36 : (rcap >= 0)) (PreH37 : (rcap <= INT_MAX)) (PreH38 : ((Zlength (l1)) = un)) (PreH39 : ((Zlength (l2)) = vn)) (PreH40 : (list_within_bound UINT_MOD l1 )) (PreH41 : (list_within_bound UINT_MOD l2 )) (PreH42 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH43 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH44 : ((last (l1) (1)) >= 1)) (PreH45 : ((last (l2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "up" ) )) # Ptr  |->_)
  **  ((( &( "vp" ) )) # Ptr  |->_)
  **  ((( &( "high" ) )) # UInt  |->_)
  **  ((( &( "t" ) )) # Ptr  |-> retval)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits ((un + vn )) (64)) * 32 )) (64)) = ((un + vn ) * 32 )) ”
.

Definition mpz_mul_partial_solve_wit_14_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (rn: Z) (un: Z) (vn: Z) (sign: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (rcap >= 0)) (PreH20 : (rcap <= INT_MAX)) (PreH21 : ((Zlength (l1)) = un)) (PreH22 : ((Zlength (l2)) = vn)) (PreH23 : (list_within_bound UINT_MOD l1 )) (PreH24 : (list_within_bound UINT_MOD l2 )) (PreH25 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH26 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH27 : ((last (l1) (1)) >= 1)) (PreH28 : ((last (l2) (1)) >= 1)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
|--
  “ ((un + vn ) > 0) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((un + vn )) (64)) * 32 )) (64)) = ((un + vn ) * 32 )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (rn = (un + vn )) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
.

Definition mpz_mul_partial_solve_wit_14 := mpz_mul_partial_solve_wit_14_pure -> mpz_mul_partial_solve_wit_14_aux.

Definition mpz_mul_partial_solve_wit_15_pure := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (un >= vn)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : ((Zlength (l1)) = un)) (PreH20 : ((Zlength (l2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1 )) (PreH22 : (list_within_bound UINT_MOD l2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH25 : ((last (l1) (1)) >= 1)) (PreH26 : ((last (l2) (1)) >= 1)) (PreH27 : (t__mp_size = 0)) (PreH28 : (t__mp_alloc = (un + vn ))) (PreH29 : (t__mp_d = rp)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
  **  (UIntArray.undef_full rp (un + vn ) )
|--
  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (vn <= un) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ”
.

Definition mpz_mul_partial_solve_wit_15_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (un >= vn)) (PreH2 : (rn = (un + vn ))) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((un + vn ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : ((Zlength (l1)) = un)) (PreH20 : ((Zlength (l2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1 )) (PreH22 : (list_within_bound UINT_MOD l2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH25 : ((last (l1) (1)) >= 1)) (PreH26 : ((last (l2) (1)) >= 1)) (PreH27 : (t__mp_size = 0)) (PreH28 : (t__mp_alloc = (un + vn ))) (PreH29 : (t__mp_d = rp)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (UIntArray.undef_full rp (un + vn ) )
|--
  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (vn <= un) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (un >= vn) ” 
  &&  “ (rn = (un + vn )) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (t__mp_size = 0) ” 
  &&  “ (t__mp_alloc = (un + vn )) ” 
  &&  “ (t__mp_d = rp) ”
  &&  (UIntArray.undef_full rp (un + vn ) )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
.

Definition mpz_mul_partial_solve_wit_15 := mpz_mul_partial_solve_wit_15_pure -> mpz_mul_partial_solve_wit_15_aux.

Definition mpz_mul_partial_solve_wit_16_pure := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (rn = (un + vn ))) (PreH2 : (un < vn)) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((vn + un ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : ((Zlength (l1)) = un)) (PreH20 : ((Zlength (l2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1 )) (PreH22 : (list_within_bound UINT_MOD l2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH25 : ((last (l1) (1)) >= 1)) (PreH26 : ((last (l2) (1)) >= 1)) (PreH27 : (t__mp_size = 0)) (PreH28 : (t__mp_alloc = (un + vn ))) (PreH29 : (t__mp_d = rp)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "vn" ) )) # Int  |-> vn)
  **  ((( &( "sign" ) )) # Int  |-> sign)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((( &( "up" ) )) # Ptr  |-> op1ptr)
  **  ((( &( "vp" ) )) # Ptr  |-> op2ptr)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  ((( &( "high" ) )) # UInt  |->_)
  **  (UIntArray.undef_full rp (vn + un ) )
|--
  “ (vn > 0) ” 
  &&  “ (un > 0) ” 
  &&  “ (un <= vn) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ”
.

Definition mpz_mul_partial_solve_wit_16_aux := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (rn = (un + vn ))) (PreH2 : (un < vn)) (PreH3 : (un > 0)) (PreH4 : (vn > 0)) (PreH5 : (0 <= sign)) (PreH6 : (sign <= 1)) (PreH7 : (mpz_mul_sign sign op1size op2size )) (PreH8 : (un <= INT_MAX)) (PreH9 : (vn <= INT_MAX)) (PreH10 : ((vn + un ) <= INT_MAX)) (PreH11 : (un = (Zabs (op1size)))) (PreH12 : (vn = (Zabs (op2size)))) (PreH13 : (op1size <> 0)) (PreH14 : (op2size <> 0)) (PreH15 : (same_sign z1 op1size )) (PreH16 : (same_sign z2 op2size )) (PreH17 : (same_sign old rsize )) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : ((Zlength (l1)) = un)) (PreH20 : ((Zlength (l2)) = vn)) (PreH21 : (list_within_bound UINT_MOD l1 )) (PreH22 : (list_within_bound UINT_MOD l2 )) (PreH23 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH24 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH25 : ((last (l1) (1)) >= 1)) (PreH26 : ((last (l2) (1)) >= 1)) (PreH27 : (t__mp_size = 0)) (PreH28 : (t__mp_alloc = (un + vn ))) (PreH29 : (t__mp_d = rp)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.undef_seg op2ptr vn op2cap )
  **  (UIntArray.undef_full rp (vn + un ) )
|--
  “ (vn > 0) ” 
  &&  “ (un > 0) ” 
  &&  “ (un <= vn) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (rn = (un + vn )) ” 
  &&  “ (un < vn) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((vn + un ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (t__mp_size = 0) ” 
  &&  “ (t__mp_alloc = (un + vn )) ” 
  &&  “ (t__mp_d = rp) ”
  &&  (UIntArray.undef_full rp (vn + un ) )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
.

Definition mpz_mul_partial_solve_wit_16 := mpz_mul_partial_solve_wit_16_pure -> mpz_mul_partial_solve_wit_16_aux.

Definition mpz_mul_partial_solve_wit_17 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (un + vn ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) ))) (PreH5 : (un >= vn)) (PreH6 : (rn = (un + vn ))) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((un + vn ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
|--
  “ ((Zlength (l_out)) = (un + vn )) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_out)) = val_out) ” 
  &&  “ (val_out = ((list_to_Z (UINT_MOD) (l1)) * (list_to_Z (UINT_MOD) (l2)) )) ” 
  &&  “ (un >= vn) ” 
  &&  “ (rn = (un + vn )) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((un + vn ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (t__mp_size = 0) ” 
  &&  “ (t__mp_alloc = (un + vn )) ” 
  &&  “ (t__mp_d = rp) ”
  &&  (((rp + (((un + vn ) - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
  **  (UIntArray.missing_i rp ((un + vn ) - 1 ) 0 (un + vn ) l_out )
  **  (UIntArray.full op1ptr un l1 )
  **  (UIntArray.full op2ptr vn l2 )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
.

Definition mpz_mul_partial_solve_wit_18 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (rn: Z) (un: Z) (vn: Z) (sign: Z) (t: Z) (t__mp_size: Z) (t__mp_alloc: Z) (t__mp_d: Z) (rp: Z) (rptr: Z) (rsize: Z) (rcap: Z) (op1ptr: Z) (op1size: Z) (op1cap: Z) (op2ptr: Z) (op2size: Z) (op2cap: Z) (l1: (@list Z)) (l2: (@list Z)) (val_out: Z) (l_out: (@list Z)) (PreH1 : ((Zlength (l_out)) = (vn + un ))) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) ))) (PreH5 : (rn = (un + vn ))) (PreH6 : (un < vn)) (PreH7 : (un > 0)) (PreH8 : (vn > 0)) (PreH9 : (0 <= sign)) (PreH10 : (sign <= 1)) (PreH11 : (mpz_mul_sign sign op1size op2size )) (PreH12 : (un <= INT_MAX)) (PreH13 : (vn <= INT_MAX)) (PreH14 : ((vn + un ) <= INT_MAX)) (PreH15 : (un = (Zabs (op1size)))) (PreH16 : (vn = (Zabs (op2size)))) (PreH17 : (op1size <> 0)) (PreH18 : (op2size <> 0)) (PreH19 : (same_sign z1 op1size )) (PreH20 : (same_sign z2 op2size )) (PreH21 : (same_sign old rsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : ((Zlength (l1)) = un)) (PreH24 : ((Zlength (l2)) = vn)) (PreH25 : (list_within_bound UINT_MOD l1 )) (PreH26 : (list_within_bound UINT_MOD l2 )) (PreH27 : ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1)))) (PreH28 : ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2)))) (PreH29 : ((last (l1) (1)) >= 1)) (PreH30 : ((last (l2) (1)) >= 1)) (PreH31 : (t__mp_size = 0)) (PreH32 : (t__mp_alloc = (un + vn ))) (PreH33 : (t__mp_d = rp)) ,
  (UIntArray.full rp (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
|--
  “ ((Zlength (l_out)) = (vn + un )) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_out)) = val_out) ” 
  &&  “ (val_out = ((list_to_Z (UINT_MOD) (l2)) * (list_to_Z (UINT_MOD) (l1)) )) ” 
  &&  “ (rn = (un + vn )) ” 
  &&  “ (un < vn) ” 
  &&  “ (un > 0) ” 
  &&  “ (vn > 0) ” 
  &&  “ (0 <= sign) ” 
  &&  “ (sign <= 1) ” 
  &&  “ (mpz_mul_sign sign op1size op2size ) ” 
  &&  “ (un <= INT_MAX) ” 
  &&  “ (vn <= INT_MAX) ” 
  &&  “ ((vn + un ) <= INT_MAX) ” 
  &&  “ (un = (Zabs (op1size))) ” 
  &&  “ (vn = (Zabs (op2size))) ” 
  &&  “ (op1size <> 0) ” 
  &&  “ (op2size <> 0) ” 
  &&  “ (same_sign z1 op1size ) ” 
  &&  “ (same_sign z2 op2size ) ” 
  &&  “ (same_sign old rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ ((Zlength (l1)) = un) ” 
  &&  “ ((Zlength (l2)) = vn) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = (Zabs (z1))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = (Zabs (z2))) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (t__mp_size = 0) ” 
  &&  “ (t__mp_alloc = (un + vn )) ” 
  &&  “ (t__mp_d = rp) ”
  &&  (((rp + (((un + vn ) - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((un + vn ) - 1 ) l_out 0))
  **  (UIntArray.missing_i rp ((un + vn ) - 1 ) 0 (vn + un ) l_out )
  **  (UIntArray.full op2ptr vn l2 )
  **  (UIntArray.full op1ptr un l1 )
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> t__mp_size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> t__mp_alloc)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> t__mp_d)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (old)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op1ptr)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op1size)
  **  ((&((op1_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op1cap)
  **  (UIntArray.undef_seg op1ptr un op1cap )
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> op2ptr)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> op2size)
  **  ((&((op2_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> op2cap)
  **  (UIntArray.undef_seg op2ptr vn op2cap )
.

Definition mpz_mul_partial_solve_wit_19 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (t: Z) ,
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z t (z1 * z2 ) )
|--
  (store_Z rop_pre old )
  **  (store_Z t (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_mul_partial_solve_wit_20 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (old: Z) (t: Z) ,
  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z t old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  (store_Z t old )
  **  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_mul_partial_solve_wit_21 := 
forall (op2_pre: Z) (op1_pre: Z) (rop_pre: Z) (z2: Z) (z1: Z) (t: Z) (ptr: Z) (cap: Z) (size: Z) ,
  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  ((&((t)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z rop_pre (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_mul_safety_wit_1 : mpz_mul_safety_wit_1.
Axiom proof_of_mpz_mul_safety_wit_2 : mpz_mul_safety_wit_2.
Axiom proof_of_mpz_mul_safety_wit_3 : mpz_mul_safety_wit_3.
Axiom proof_of_mpz_mul_safety_wit_4 : mpz_mul_safety_wit_4.
Axiom proof_of_mpz_mul_safety_wit_5 : mpz_mul_safety_wit_5.
Axiom proof_of_mpz_mul_safety_wit_6 : mpz_mul_safety_wit_6.
Axiom proof_of_mpz_mul_safety_wit_7 : mpz_mul_safety_wit_7.
Axiom proof_of_mpz_mul_safety_wit_8 : mpz_mul_safety_wit_8.
Axiom proof_of_mpz_mul_safety_wit_9 : mpz_mul_safety_wit_9.
Axiom proof_of_mpz_mul_safety_wit_10 : mpz_mul_safety_wit_10.
Axiom proof_of_mpz_mul_safety_wit_11 : mpz_mul_safety_wit_11.
Axiom proof_of_mpz_mul_safety_wit_12 : mpz_mul_safety_wit_12.
Axiom proof_of_mpz_mul_safety_wit_13 : mpz_mul_safety_wit_13.
Axiom proof_of_mpz_mul_safety_wit_14 : mpz_mul_safety_wit_14.
Axiom proof_of_mpz_mul_safety_wit_15 : mpz_mul_safety_wit_15.
Axiom proof_of_mpz_mul_safety_wit_16 : mpz_mul_safety_wit_16.
Axiom proof_of_mpz_mul_safety_wit_17 : mpz_mul_safety_wit_17.
Axiom proof_of_mpz_mul_safety_wit_18 : mpz_mul_safety_wit_18.
Axiom proof_of_mpz_mul_safety_wit_19 : mpz_mul_safety_wit_19.
Axiom proof_of_mpz_mul_safety_wit_20 : mpz_mul_safety_wit_20.
Axiom proof_of_mpz_mul_safety_wit_21 : mpz_mul_safety_wit_21.
Axiom proof_of_mpz_mul_safety_wit_22 : mpz_mul_safety_wit_22.
Axiom proof_of_mpz_mul_safety_wit_23 : mpz_mul_safety_wit_23.
Axiom proof_of_mpz_mul_safety_wit_24 : mpz_mul_safety_wit_24.
Axiom proof_of_mpz_mul_safety_wit_25 : mpz_mul_safety_wit_25.
Axiom proof_of_mpz_mul_safety_wit_26 : mpz_mul_safety_wit_26.
Axiom proof_of_mpz_mul_safety_wit_27 : mpz_mul_safety_wit_27.
Axiom proof_of_mpz_mul_safety_wit_28 : mpz_mul_safety_wit_28.
Axiom proof_of_mpz_mul_safety_wit_29 : mpz_mul_safety_wit_29.
Axiom proof_of_mpz_mul_safety_wit_30 : mpz_mul_safety_wit_30.
Axiom proof_of_mpz_mul_safety_wit_31 : mpz_mul_safety_wit_31.
Axiom proof_of_mpz_mul_safety_wit_32 : mpz_mul_safety_wit_32.
Axiom proof_of_mpz_mul_safety_wit_33 : mpz_mul_safety_wit_33.
Axiom proof_of_mpz_mul_safety_wit_34 : mpz_mul_safety_wit_34.
Axiom proof_of_mpz_mul_safety_wit_35 : mpz_mul_safety_wit_35.
Axiom proof_of_mpz_mul_safety_wit_36 : mpz_mul_safety_wit_36.
Axiom proof_of_mpz_mul_safety_wit_37 : mpz_mul_safety_wit_37.
Axiom proof_of_mpz_mul_entail_wit_1_1 : mpz_mul_entail_wit_1_1.
Axiom proof_of_mpz_mul_entail_wit_1_2 : mpz_mul_entail_wit_1_2.
Axiom proof_of_mpz_mul_entail_wit_1_3 : mpz_mul_entail_wit_1_3.
Axiom proof_of_mpz_mul_entail_wit_1_4 : mpz_mul_entail_wit_1_4.
Axiom proof_of_mpz_mul_entail_wit_2 : mpz_mul_entail_wit_2.
Axiom proof_of_mpz_mul_entail_wit_3 : mpz_mul_entail_wit_3.
Axiom proof_of_mpz_mul_entail_wit_4_1 : mpz_mul_entail_wit_4_1.
Axiom proof_of_mpz_mul_entail_wit_4_2 : mpz_mul_entail_wit_4_2.
Axiom proof_of_mpz_mul_entail_wit_4_3 : mpz_mul_entail_wit_4_3.
Axiom proof_of_mpz_mul_entail_wit_4_4 : mpz_mul_entail_wit_4_4.
Axiom proof_of_mpz_mul_entail_wit_4_5 : mpz_mul_entail_wit_4_5.
Axiom proof_of_mpz_mul_entail_wit_4_6 : mpz_mul_entail_wit_4_6.
Axiom proof_of_mpz_mul_entail_wit_4_7 : mpz_mul_entail_wit_4_7.
Axiom proof_of_mpz_mul_entail_wit_4_8 : mpz_mul_entail_wit_4_8.
Axiom proof_of_mpz_mul_return_wit_1 : mpz_mul_return_wit_1.
Axiom proof_of_mpz_mul_return_wit_2 : mpz_mul_return_wit_2.
Axiom proof_of_mpz_mul_return_wit_3 : mpz_mul_return_wit_3.
Axiom proof_of_mpz_mul_partial_solve_wit_1 : mpz_mul_partial_solve_wit_1.
Axiom proof_of_mpz_mul_partial_solve_wit_2 : mpz_mul_partial_solve_wit_2.
Axiom proof_of_mpz_mul_partial_solve_wit_3 : mpz_mul_partial_solve_wit_3.
Axiom proof_of_mpz_mul_partial_solve_wit_4 : mpz_mul_partial_solve_wit_4.
Axiom proof_of_mpz_mul_partial_solve_wit_5_pure : mpz_mul_partial_solve_wit_5_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_5 : mpz_mul_partial_solve_wit_5.
Axiom proof_of_mpz_mul_partial_solve_wit_6_pure : mpz_mul_partial_solve_wit_6_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_6 : mpz_mul_partial_solve_wit_6.
Axiom proof_of_mpz_mul_partial_solve_wit_7_pure : mpz_mul_partial_solve_wit_7_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_7 : mpz_mul_partial_solve_wit_7.
Axiom proof_of_mpz_mul_partial_solve_wit_8_pure : mpz_mul_partial_solve_wit_8_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_8 : mpz_mul_partial_solve_wit_8.
Axiom proof_of_mpz_mul_partial_solve_wit_9_pure : mpz_mul_partial_solve_wit_9_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_9 : mpz_mul_partial_solve_wit_9.
Axiom proof_of_mpz_mul_partial_solve_wit_10_pure : mpz_mul_partial_solve_wit_10_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_10 : mpz_mul_partial_solve_wit_10.
Axiom proof_of_mpz_mul_partial_solve_wit_11_pure : mpz_mul_partial_solve_wit_11_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_11 : mpz_mul_partial_solve_wit_11.
Axiom proof_of_mpz_mul_partial_solve_wit_12_pure : mpz_mul_partial_solve_wit_12_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_12 : mpz_mul_partial_solve_wit_12.
Axiom proof_of_mpz_mul_partial_solve_wit_13 : mpz_mul_partial_solve_wit_13.
Axiom proof_of_mpz_mul_partial_solve_wit_14_pure : mpz_mul_partial_solve_wit_14_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_14 : mpz_mul_partial_solve_wit_14.
Axiom proof_of_mpz_mul_partial_solve_wit_15_pure : mpz_mul_partial_solve_wit_15_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_15 : mpz_mul_partial_solve_wit_15.
Axiom proof_of_mpz_mul_partial_solve_wit_16_pure : mpz_mul_partial_solve_wit_16_pure.
Axiom proof_of_mpz_mul_partial_solve_wit_16 : mpz_mul_partial_solve_wit_16.
Axiom proof_of_mpz_mul_partial_solve_wit_17 : mpz_mul_partial_solve_wit_17.
Axiom proof_of_mpz_mul_partial_solve_wit_18 : mpz_mul_partial_solve_wit_18.
Axiom proof_of_mpz_mul_partial_solve_wit_19 : mpz_mul_partial_solve_wit_19.
Axiom proof_of_mpz_mul_partial_solve_wit_20 : mpz_mul_partial_solve_wit_20.
Axiom proof_of_mpz_mul_partial_solve_wit_21 : mpz_mul_partial_solve_wit_21.

End VC_Correct.
