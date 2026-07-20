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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_strategy_proof.

(*----- Function mpz_gcd -----*)

Definition mpz_gcd_safety_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign zu size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "gz" ) )) # UInt64  |->_)
  **  ((( &( "vz" ) )) # UInt64  |->_)
  **  ((( &( "uz" ) )) # UInt64  |->_)
  **  ((( &( "tv" ) )) # Ptr  |->_)
  **  ((( &( "tu" ) )) # Ptr  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zv size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (size <> 0)) (PreH4 : (same_sign zu size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "gz" ) )) # UInt64  |->_)
  **  ((( &( "vz" ) )) # UInt64  |->_)
  **  ((( &( "uz" ) )) # UInt64  |->_)
  **  ((( &( "tv" ) )) # Ptr  |->_)
  **  ((( &( "tu" ) )) # Ptr  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (store_Z g_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign rv size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH4 : (size < size_2)) (PreH5 : (same_sign odd_2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign odd size )) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (retval_3 < retval_4)) (PreH10 : (0 <= retval_4)) (PreH11 : (odd_2 > 0)) (PreH12 : ((odd_2 % ( 2 ) ) = 1)) (PreH13 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH14 : (0 <= retval_3)) (PreH15 : (odd > 0)) (PreH16 : ((odd % ( 2 ) ) = 1)) (PreH17 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval <> 0)) (PreH20 : ((Zabs (zu)) > 0)) (PreH21 : ((Zabs (zv)) > 0)) (PreH22 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_3)
  **  (store_Z g_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_4 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign rv size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH4 : (size < size_2)) (PreH5 : (same_sign odd_2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign odd size )) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (retval_3 >= retval_4)) (PreH10 : (0 <= retval_4)) (PreH11 : (odd_2 > 0)) (PreH12 : ((odd_2 % ( 2 ) ) = 1)) (PreH13 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH14 : (0 <= retval_3)) (PreH15 : (odd > 0)) (PreH16 : ((odd % ( 2 ) ) = 1)) (PreH17 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval <> 0)) (PreH20 : ((Zabs (zu)) > 0)) (PreH21 : ((Zabs (zv)) > 0)) (PreH22 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_4)
  **  (store_Z g_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_5 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign rv size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH4 : (size >= size_2)) (PreH5 : (same_sign odd_2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign odd size )) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (retval_3 < retval_4)) (PreH10 : (0 <= retval_4)) (PreH11 : (odd_2 > 0)) (PreH12 : ((odd_2 % ( 2 ) ) = 1)) (PreH13 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH14 : (0 <= retval_3)) (PreH15 : (odd > 0)) (PreH16 : ((odd % ( 2 ) ) = 1)) (PreH17 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval <> 0)) (PreH20 : ((Zabs (zu)) > 0)) (PreH21 : ((Zabs (zv)) > 0)) (PreH22 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_3)
  **  (store_Z g_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_6 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign rv size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH4 : (size >= size_2)) (PreH5 : (same_sign odd_2 size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign odd size )) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (retval_3 >= retval_4)) (PreH10 : (0 <= retval_4)) (PreH11 : (odd_2 > 0)) (PreH12 : ((odd_2 % ( 2 ) ) = 1)) (PreH13 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH14 : (0 <= retval_3)) (PreH15 : (odd > 0)) (PreH16 : ((odd % ( 2 ) ) = 1)) (PreH17 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval <> 0)) (PreH20 : ((Zabs (zu)) > 0)) (PreH21 : ((Zabs (zv)) > 0)) (PreH22 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_4)
  **  (store_Z g_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_7 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (tu_v > 0)) (PreH5 : (tv_v > 0)) (PreH6 : ((tv_v % ( 2 ) ) = 1)) (PreH7 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH8 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_gcd_safety_wit_8 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (odd < tv_v)) (PreH2 : (retval_2 = (-1))) (PreH3 : (0 <= retval)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (tu <> 0)) (PreH8 : (tv <> 0)) (PreH9 : (gz_v >= 0)) (PreH10 : (tu_v > 0)) (PreH11 : (tv_v > 0)) (PreH12 : ((tv_v % ( 2 ) ) = 1)) (PreH13 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH14 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_9 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (odd = tv_v)) (PreH2 : (retval_2 = 0)) (PreH3 : (0 <= retval)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (tu <> 0)) (PreH8 : (tv <> 0)) (PreH9 : (gz_v >= 0)) (PreH10 : (tu_v > 0)) (PreH11 : (tv_v > 0)) (PreH12 : ((tv_v % ( 2 ) ) = 1)) (PreH13 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH14 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_10 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (odd > tv_v)) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= retval)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (tu <> 0)) (PreH8 : (tv <> 0)) (PreH9 : (gz_v >= 0)) (PreH10 : (tu_v > 0)) (PreH11 : (tv_v > 0)) (PreH12 : ((tv_v % ( 2 ) ) = 1)) (PreH13 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH14 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_11 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (odd < tv_v)) (PreH3 : (retval_2 = (-1))) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ False ”
.

Definition mpz_gcd_safety_wit_12 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (odd = tv_v)) (PreH3 : (retval_2 = 0)) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ False ”
.

Definition mpz_gcd_safety_wit_13 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (odd > tv_v)) (PreH3 : (retval_2 = 1)) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ False ”
.

Definition mpz_gcd_safety_wit_14 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (odd < tv_v)) (PreH3 : (retval_2 = (-1))) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_15 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (odd > tv_v)) (PreH3 : (retval_2 = 1)) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_16 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (odd < tv_v)) (PreH4 : (retval_2 = (-1))) (PreH5 : (0 <= retval)) (PreH6 : (odd > 0)) (PreH7 : ((odd % ( 2 ) ) = 1)) (PreH8 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH9 : (tu <> 0)) (PreH10 : (tv <> 0)) (PreH11 : (gz_v >= 0)) (PreH12 : (tu_v > 0)) (PreH13 : (tv_v > 0)) (PreH14 : ((tv_v % ( 2 ) ) = 1)) (PreH15 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH16 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ False ”
.

Definition mpz_gcd_safety_wit_17 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (odd > tv_v)) (PreH4 : (retval_2 = 1)) (PreH5 : (0 <= retval)) (PreH6 : (odd > 0)) (PreH7 : ((odd % ( 2 ) ) = 1)) (PreH8 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH9 : (tu <> 0)) (PreH10 : (tv <> 0)) (PreH11 : (gz_v >= 0)) (PreH12 : (tu_v > 0)) (PreH13 : (tv_v > 0)) (PreH14 : ((tv_v % ( 2 ) ) = 1)) (PreH15 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH16 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ False ”
.

Definition mpz_gcd_safety_wit_18 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign odd size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (retval_2 < 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (odd < tv_v)) (PreH6 : (retval_2 = (-1))) (PreH7 : (0 <= retval)) (PreH8 : (odd > 0)) (PreH9 : ((odd % ( 2 ) ) = 1)) (PreH10 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH11 : (tu <> 0)) (PreH12 : (tv <> 0)) (PreH13 : (gz_v >= 0)) (PreH14 : (tu_v > 0)) (PreH15 : (tv_v > 0)) (PreH16 : ((tv_v % ( 2 ) ) = 1)) (PreH17 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH18 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_gcd_safety_wit_19 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign tv_v size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (retval_2 >= 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (odd > tv_v)) (PreH6 : (retval_2 = 1)) (PreH7 : (0 <= retval)) (PreH8 : (odd > 0)) (PreH9 : ((odd % ( 2 ) ) = 1)) (PreH10 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH11 : (tu <> 0)) (PreH12 : (tv <> 0)) (PreH13 : (gz_v >= 0)) (PreH14 : (tu_v > 0)) (PreH15 : (tv_v > 0)) (PreH16 : ((tv_v % ( 2 ) ) = 1)) (PreH17 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH18 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu odd )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_gcd_safety_wit_20 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (cval: Z) (qv: Z) (rv: Z) (gptr: Z) (gsize: Z) (gcap: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (mpz_div_qr_math 2 tu_v tv_v qv rv )) (PreH4 : (gz_v >= 0)) (PreH5 : (tu_v > 0)) (PreH6 : (tv_v > 0)) (PreH7 : (tv_v <= UINT_MAX)) (PreH8 : ((tv_v % ( 2 ) ) = 1)) (PreH9 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH10 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) (PreH11 : (gcap >= 0)) (PreH12 : (gcap <= INT_MAX)) (PreH13 : ((Zabs (gsize)) <= gcap)) (PreH14 : (same_sign old gsize )) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> gptr)
  **  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  ((( &( "gp" ) )) # Ptr  |->_)
  **  (mpd_store_Z_compact UINT_MOD gptr (Zabs (old)) (Zabs (gsize)) )
  **  (UIntArray.undef_seg gptr (Zabs (gsize)) gcap )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_gcd_safety_wit_21 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val > 0)) (PreH6 : (vsize = 1)) (PreH7 : (gcap >= 0)) (PreH8 : (gcap <= INT_MAX)) (PreH9 : ((Zabs (gsize)) <= gcap)) (PreH10 : (same_sign old gsize )) (PreH11 : (0 <= rem)) (PreH12 : (rem <= UINT_MAX)) (PreH13 : (0 <= tv_val)) (PreH14 : (tv_val <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH16 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH17 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH18 : ((Zlength (vdata)) = 1)) (PreH19 : ((last (tdata) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata )) (PreH21 : (list_within_bound UINT_MOD vdata )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH26 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_22 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val > 0)) (PreH6 : (vsize = 1)) (PreH7 : (gcap >= 0)) (PreH8 : (gcap <= INT_MAX)) (PreH9 : ((Zabs (gsize)) <= gcap)) (PreH10 : (same_sign old gsize )) (PreH11 : (0 <= rem)) (PreH12 : (rem <= UINT_MAX)) (PreH13 : (0 <= tv_val)) (PreH14 : (tv_val <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH16 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH17 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH18 : ((Zlength (vdata)) = 1)) (PreH19 : ((last (tdata) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata )) (PreH21 : (list_within_bound UINT_MOD vdata )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH26 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_safety_wit_23 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0))))) (PreH2 : (tu <> 0)) (PreH3 : (tv <> 0)) (PreH4 : (gp = g__mp_d)) (PreH5 : (gz_v >= 0)) (PreH6 : (tv_val > 0)) (PreH7 : (vsize = 1)) (PreH8 : (gcap >= 0)) (PreH9 : (gcap <= INT_MAX)) (PreH10 : ((Zabs (gsize)) <= gcap)) (PreH11 : (same_sign old gsize )) (PreH12 : (0 <= rem)) (PreH13 : (rem <= UINT_MAX)) (PreH14 : (0 <= tv_val)) (PreH15 : (tv_val <= UINT_MAX)) (PreH16 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH17 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH18 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH19 : ((Zlength (vdata)) = 1)) (PreH20 : ((last (tdata) (1)) >= 1)) (PreH21 : (list_within_bound UINT_MOD tdata )) (PreH22 : (list_within_bound UINT_MOD vdata )) (PreH23 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH24 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH25 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH26 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH27 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |-> retval)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_gcd_entail_wit_1 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z g_pre old )
|--
  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
|--
  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ ((Zabs (zu)) > 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
).

Definition mpz_gcd_entail_wit_1_split_goal_1 := 
forall (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
|--
  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
.

Definition mpz_gcd_entail_wit_1_split_goal_2 := 
forall (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
|--
  “ ((Zabs (zv)) > 0) ”
.

Definition mpz_gcd_entail_wit_1_split_goal_3 := 
forall (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
|--
  “ ((Zabs (zu)) > 0) ”
.

Definition mpz_gcd_entail_wit_1_split_goal_spatial := 
forall (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_entail_wit_2_1 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z retval tu_v )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (same_sign tu_v size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_v)) (Zabs (size_3)) )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_2_2 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z retval tu_v )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (same_sign tu_v size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_v)) (Zabs (size_3)) )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_2_3 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z retval tu_v )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (same_sign tu_v size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_v)) (Zabs (size_3)) )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_2_4 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z retval tu_v )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 <> 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (same_sign tu_v size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (retval_3)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_v)) (Zabs (size_3)) )
  **  (store_Z retval_2 tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v_2: Z) (tv_v_2: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (tu_v_2 > 0)) (PreH5 : (tv_v_2 > 0)) (PreH6 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH7 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH8 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (store_Z tu tu_v_2 )
  **  (store_Z tv tv_v_2 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_entail_wit_4_1 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 1)) (PreH2 : (same_sign odd size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd < tv_v_2)) (PreH7 : (retval_2 = (-1))) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu tv_v_2 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 1)) (PreH2 : (same_sign odd size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd < tv_v_2)) (PreH7 : (retval_2 = (-1))) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  (store_Z tu tv_v_2 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (same_sign tv_v size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  (store_Z tu tu_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_4_2 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 1)) (PreH2 : (same_sign tv_v_2 size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd > tv_v_2)) (PreH7 : (retval_2 = 1)) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v_2)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 1)) (PreH2 : (same_sign tv_v_2 size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd > tv_v_2)) (PreH7 : (retval_2 = 1)) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v_2)) (Zabs (size)) )
  **  (store_Z tu odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (same_sign tv_v size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  (store_Z tu tu_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_5 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v_2: Z) (tv_v_2: Z) (gz_v: Z) (tu: Z) (tv: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (tu = tu)) (PreH2 : (mpz_div_qr_math 2 tu_v_2 tv_v_2 qv_2 rv_2 )) (PreH3 : (tu <> 0)) (PreH4 : (tv <> 0)) (PreH5 : (gz_v >= 0)) (PreH6 : (tu_v_2 > 0)) (PreH7 : (tv_v_2 > 0)) (PreH8 : (tv_v_2 <= UINT_MAX)) (PreH9 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH10 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH11 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (store_Z_read0 tu rv_2 )
  **  (store_Z tv tv_v_2 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (gptr: Z)  (gsize: Z)  (gcap: Z)  (tu_v: Z)  (tv_v: Z)  (qv: Z)  (rv: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (mpz_div_qr_math 2 tu_v tv_v qv rv ) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ”
  &&  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> gptr)
  **  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  (mpd_store_Z_compact UINT_MOD gptr (Zabs (old)) (Zabs (gsize)) )
  **  (UIntArray.undef_seg gptr (Zabs (gsize)) gcap )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v_2: Z) (tv_v_2: Z) (gz_v: Z) (tu: Z) (tv: Z) (qv_2: Z) (rv_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign old size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (mpz_div_qr_math 2 tu_v_2 tv_v_2 qv_2 rv_2 )) (PreH4 : (tu <> 0)) (PreH5 : (tv <> 0)) (PreH6 : (gz_v >= 0)) (PreH7 : (tu_v_2 > 0)) (PreH8 : (tv_v_2 > 0)) (PreH9 : (tv_v_2 <= UINT_MAX)) (PreH10 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH11 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH12 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
  **  (store_Z_read0 tu rv_2 )
  **  (store_Z tv tv_v_2 )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tu_v: Z)  (tv_v: Z)  (qv: Z)  (rv: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (mpz_div_qr_math 2 tu_v tv_v qv rv ) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign old size ) ”
  &&  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_6 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (gz_v: Z) (qv: Z) (rv: Z) (gsize_2: Z) (gcap_2: Z) (tu: Z) (tv: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign old gsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max (1) (gcap_2)))) (PreH3 : (tu <> 0)) (PreH4 : (tv <> 0)) (PreH5 : (mpz_div_qr_math 2 tu_v tv_v qv rv )) (PreH6 : (gz_v >= 0)) (PreH7 : (tu_v > 0)) (PreH8 : (tv_v > 0)) (PreH9 : (tv_v <= UINT_MAX)) (PreH10 : ((tv_v % ( 2 ) ) = 1)) (PreH11 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH12 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) (PreH13 : (gcap_2 >= 0)) (PreH14 : (gcap_2 <= INT_MAX)) (PreH15 : ((Zabs (gsize_2)) <= gcap_2)) (PreH16 : (same_sign old gsize_2 )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (old)) (Zabs (gsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (gsize_2)) (Z.max (1) (gcap_2)) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize_2)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (g__mp_alloc: Z)  (vptr: Z)  (vcap: Z)  (tptr: Z)  (tcap: Z)  (tsize: Z)  (vdata: (@list Z))  (tdata: (@list Z))  (rem: Z)  (gsize: Z)  (gcap: Z)  (vsize: Z)  (tv_val: Z)  (g__mp_d: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (retval = g__mp_d) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tv_val > 0) ” 
  &&  “ (vsize = 1) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ” 
  &&  “ (0 <= rem) ” 
  &&  “ (rem <= UINT_MAX) ” 
  &&  “ (0 <= tv_val) ” 
  &&  “ (tv_val <= UINT_MAX) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem) ” 
  &&  “ ((Znth (0) (vdata) (0)) = tv_val) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (tsize))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = rem) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = tv_val) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) )) ” 
  &&  “ (g__mp_alloc = (Z.max (1) (gcap))) ”
  &&  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.full tptr (Zmax ((Zabs (tsize))) (1)) (mpd_read0_data (tdata)) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.full vptr 1 vdata )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (old)) (Zabs (gsize)) )
  **  (UIntArray.undef_seg retval (Zabs (gsize)) (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (gz_v: Z) (qv: Z) (rv: Z) (gsize_2: Z) (gcap_2: Z) (tu: Z) (tv: Z) (z_callee__mp_alloc: Z) (retval: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign rv size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign tv_v size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (same_sign old gsize_2 )) (PreH6 : (z_callee__mp_alloc = (Z.max (1) (gcap_2)))) (PreH7 : (tu <> 0)) (PreH8 : (tv <> 0)) (PreH9 : (mpz_div_qr_math 2 tu_v tv_v qv rv )) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : (tv_v <= UINT_MAX)) (PreH14 : ((tv_v % ( 2 ) ) = 1)) (PreH15 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH16 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) (PreH17 : (gcap_2 >= 0)) (PreH18 : (gcap_2 <= INT_MAX)) (PreH19 : ((Zabs (gsize_2)) <= gcap_2)) (PreH20 : (same_sign old gsize_2 )) ,
  (mpd_store_Z_compact_read0 ptr_2 (Zabs (rv)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (old)) (Zabs (gsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (gsize_2)) (Z.max (1) (gcap_2)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (vdata: (@list Z))  (tdata: (@list Z))  (gcap: Z) ,
  “ (size = 1) ” 
  &&  “ (z_callee__mp_alloc = (Z.max (1) (gcap))) ” 
  &&  “ (z_callee__mp_alloc = (Z.max (1) (gcap))) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ ((Znth (0) (vdata) (0)) > 0) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize_2)) <= gcap) ” 
  &&  “ (same_sign old gsize_2 ) ” 
  &&  “ (0 <= (Znth (0) ((mpd_read0_data (tdata))) (0))) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0) (vdata) (0))) ” 
  &&  “ ((Znth (0) (vdata) (0)) <= UINT_MAX) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (size_2))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = (Znth (0) ((mpd_read0_data (tdata))) (0))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = (Znth (0) (vdata) (0))) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd ((Znth (0) ((mpd_read0_data (tdata))) (0))) ((Znth (0) (vdata) (0)))) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd ((Znth (0) ((mpd_read0_data (tdata))) (0))) ((Znth (0) (vdata) (0)))) )) ”
  &&  (UIntArray.full ptr_2 (Zmax ((Zabs (size_2))) (1)) (mpd_read0_data (tdata)) )
  **  (UIntArray.full ptr 1 vdata )
  **  (UIntArray.undef_seg ptr 1 cap )
  **  (mpd_store_Z_compact UINT_MOD retval (Zabs (old)) (Zabs (gsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (gsize_2)) (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_7 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem_2: Z) (tv_val_2: Z) (tptr_2: Z) (tsize_2: Z) (tcap_2: Z) (tdata_2: (@list Z)) (vptr_2: Z) (vsize_2: Z) (vcap_2: Z) (vdata_2: (@list Z)) (gsize_2: Z) (gcap_2: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d_2: Z) (g__mp_alloc_2: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d_2)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val_2 > 0)) (PreH6 : (vsize_2 = 1)) (PreH7 : (gcap_2 >= 0)) (PreH8 : (gcap_2 <= INT_MAX)) (PreH9 : ((Zabs (gsize_2)) <= gcap_2)) (PreH10 : (same_sign old gsize_2 )) (PreH11 : (0 <= rem_2)) (PreH12 : (rem_2 <= UINT_MAX)) (PreH13 : (0 <= tv_val_2)) (PreH14 : (tv_val_2 <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata_2))) (0)) = rem_2)) (PreH16 : ((Znth (0) (vdata_2) (0)) = tv_val_2)) (PreH17 : ((Zlength (tdata_2)) = (Zabs (tsize_2)))) (PreH18 : ((Zlength (vdata_2)) = 1)) (PreH19 : ((last (tdata_2) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata_2 )) (PreH21 : (list_within_bound UINT_MOD vdata_2 )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata_2)) = rem_2)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata_2)) = tv_val_2)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem_2) (tv_val_2)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem_2) (tv_val_2)) ))) (PreH26 : (g__mp_alloc_2 = (Z.max (1) (gcap_2)))) ,
  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d_2)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize_2)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap_2)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr_2)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize_2)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc_2)
  **  (UIntArray.full tptr_2 (Zmax ((Zabs (tsize_2))) (1)) (mpd_read0_data (tdata_2)) )
  **  (UIntArray.undef_seg tptr_2 (Zmax ((Zabs (tsize_2))) (1)) tcap_2 )
  **  (UIntArray.full vptr_2 1 vdata_2 )
  **  (UIntArray.undef_seg vptr_2 1 vcap_2 )
  **  (mpd_store_Z_compact UINT_MOD gp (Zabs (old)) (Zabs (gsize_2)) )
  **  (UIntArray.undef_seg gp (Zabs (gsize_2)) (Z.max (1) (gcap_2)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (g__mp_alloc: Z)  (vptr: Z)  (vcap: Z)  (tptr: Z)  (tcap: Z)  (tsize: Z)  (vdata: (@list Z))  (tdata: (@list Z))  (rem: Z)  (gsize: Z)  (gcap: Z)  (vsize: Z)  (tv_val: Z)  (g__mp_d: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gp = g__mp_d) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tv_val > 0) ” 
  &&  “ (vsize = 1) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ” 
  &&  “ (0 <= rem) ” 
  &&  “ (rem <= UINT_MAX) ” 
  &&  “ (0 <= tv_val) ” 
  &&  “ (tv_val <= UINT_MAX) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem) ” 
  &&  “ ((Znth (0) (vdata) (0)) = tv_val) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (tsize))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = rem) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = tv_val) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) )) ” 
  &&  “ (g__mp_alloc = (Z.max (1) (gcap))) ”
  &&  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem_2: Z) (tv_val_2: Z) (tptr_2: Z) (tsize_2: Z) (tdata_2: (@list Z)) (vptr_2: Z) (vsize_2: Z) (vdata_2: (@list Z)) (gsize_2: Z) (gcap_2: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d_2: Z) (g__mp_alloc_2: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d_2)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val_2 > 0)) (PreH6 : (vsize_2 = 1)) (PreH7 : (gcap_2 >= 0)) (PreH8 : (gcap_2 <= INT_MAX)) (PreH9 : ((Zabs (gsize_2)) <= gcap_2)) (PreH10 : (same_sign old gsize_2 )) (PreH11 : (0 <= rem_2)) (PreH12 : (rem_2 <= UINT_MAX)) (PreH13 : (0 <= tv_val_2)) (PreH14 : (tv_val_2 <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata_2))) (0)) = rem_2)) (PreH16 : ((Znth (0) (vdata_2) (0)) = tv_val_2)) (PreH17 : ((Zlength (tdata_2)) = (Zabs (tsize_2)))) (PreH18 : ((Zlength (vdata_2)) = 1)) (PreH19 : ((last (tdata_2) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata_2 )) (PreH21 : (list_within_bound UINT_MOD vdata_2 )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata_2)) = rem_2)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata_2)) = tv_val_2)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem_2) (tv_val_2)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem_2) (tv_val_2)) ))) (PreH26 : (g__mp_alloc_2 = (Z.max (1) (gcap_2)))) ,
  (UIntArray.full tptr_2 (Zmax ((Zabs (tsize_2))) (1)) (mpd_read0_data (tdata_2)) )
  **  (UIntArray.full vptr_2 1 vdata_2 )
  **  (mpd_store_Z_compact UINT_MOD gp (Zabs (old)) (Zabs (gsize_2)) )
  **  (UIntArray.undef_seg gp (Zabs (gsize_2)) (Z.max (1) (gcap_2)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (x: Z)  (vdata: (@list Z))  (tdata: (@list Z))  (gcap: Z) ,
  “ (g__mp_alloc_2 = (Z.max (1) (gcap))) ” 
  &&  “ (vsize_2 = 1) ” 
  &&  “ (g__mp_alloc_2 = (Z.max (1) (gcap))) ” 
  &&  “ (vsize_2 = 1) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gp = g__mp_d_2) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ ((Znth (0) (vdata) (0)) > 0) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize_2)) <= gcap) ” 
  &&  “ (same_sign old gsize_2 ) ” 
  &&  “ (0 <= (Znth (0) ((mpd_read0_data (tdata))) (0))) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0) (vdata) (0))) ” 
  &&  “ ((Znth (0) (vdata) (0)) <= UINT_MAX) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (tsize_2))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = (Znth (0) ((mpd_read0_data (tdata))) (0))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = (Znth (0) (vdata) (0))) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd ((Znth (0) ((mpd_read0_data (tdata))) (0))) ((Znth (0) (vdata) (0)))) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd ((Znth (0) ((mpd_read0_data (tdata))) (0))) ((Znth (0) (vdata) (0)))) )) ”
  &&  ((gp) # UInt  |-> x)
  **  (UIntArray.seg tptr_2 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg tptr_2 1 (Zmax ((Zabs (tsize_2))) (1)) (sublist (1) ((Zmax ((Zabs (tsize_2))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg vptr_2 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_8_1 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign odd size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd < tv_v_2)) (PreH7 : (retval_2 = (-1))) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (store_Z tu (tv_v_2 - odd ) )
  **  (store_Z tv odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign odd size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd < tv_v_2)) (PreH7 : (retval_2 = (-1))) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (store_Z tu (tv_v_2 - odd ) )
  **  (store_Z tv odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_8_2 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign tv_v_2 size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd > tv_v_2)) (PreH7 : (retval_2 = 1)) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (store_Z tu (odd - tv_v_2 ) )
  **  (store_Z tv tv_v_2 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v_2: Z) (tu_v_2: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign tv_v_2 size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd > tv_v_2)) (PreH7 : (retval_2 = 1)) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v_2 = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v_2 > 0)) (PreH16 : (tv_v_2 > 0)) (PreH17 : ((tv_v_2 % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v_2) (tv_v_2)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v_2) (tv_v_2)) ))) ,
  (store_Z tu (odd - tv_v_2 ) )
  **  (store_Z tv tv_v_2 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_v: Z)  (tu_v: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_1 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd )
  **  (store_Z retval_2 old )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z retval tu_final )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd )
  **  (store_Z retval_2 old )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (same_sign tu_final size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_final)) (Zabs (size_3)) )
  **  (store_Z g_pre g_odd )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_2 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd )
  **  (store_Z retval_2 old )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z retval tu_final )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd )
  **  (store_Z retval_2 old )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (same_sign tu_final size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_final)) (Zabs (size_3)) )
  **  (store_Z g_pre g_odd )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_3 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd_2 )
  **  (store_Z retval_2 old )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z retval tu_final )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd_2 )
  **  (store_Z retval_2 old )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (same_sign tu_final size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_final)) (Zabs (size_3)) )
  **  (store_Z g_pre g_odd )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_4 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd_2 )
  **  (store_Z retval_2 old )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z retval tu_final )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_4: Z) (odd_2: Z) (retval_3: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_4 >= retval_3)) (PreH11 : (0 <= retval_3)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_3)) ))) (PreH15 : (0 <= retval_4)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_4)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre odd_2 )
  **  (store_Z retval_2 old )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (same_sign tu_final size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd retval_3 ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (retval_3)) )) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tu_final)) (Zabs (size_3)) )
  **  (store_Z g_pre g_odd )
  **  (store_Z retval_2 tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_5 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (odd = tv_v)) (PreH3 : (retval_2 = 0)) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z g_pre odd )
  **  (store_Z tu old )
  **  (store_Z tv tv_v )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z tu tu_final )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (odd = tv_v)) (PreH3 : (retval_2 = 0)) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z g_pre odd )
  **  (store_Z tu old )
  **  (store_Z tv tv_v )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z tu tu_final )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_6 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zgcd ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0))))) (PreH3 : (tu <> 0)) (PreH4 : (tv <> 0)) (PreH5 : (gp = g__mp_d)) (PreH6 : (gz_v >= 0)) (PreH7 : (tv_val > 0)) (PreH8 : (vsize = 1)) (PreH9 : (gcap >= 0)) (PreH10 : (gcap <= INT_MAX)) (PreH11 : ((Zabs (gsize)) <= gcap)) (PreH12 : (same_sign old gsize )) (PreH13 : (0 <= rem)) (PreH14 : (rem <= UINT_MAX)) (PreH15 : (0 <= tv_val)) (PreH16 : (tv_val <= UINT_MAX)) (PreH17 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH18 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH19 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH20 : ((Zlength (vdata)) = 1)) (PreH21 : ((last (tdata) (1)) >= 1)) (PreH22 : (list_within_bound UINT_MOD tdata )) (PreH23 : (list_within_bound UINT_MOD vdata )) (PreH24 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH25 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH26 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH27 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH28 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |-> retval)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z tu tu_final )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (retval = 0)) (PreH4 : (retval = (Zgcd ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0))))) (PreH5 : (tu <> 0)) (PreH6 : (tv <> 0)) (PreH7 : (gp = g__mp_d)) (PreH8 : (gz_v >= 0)) (PreH9 : (tv_val > 0)) (PreH10 : (vsize = 1)) (PreH11 : (gcap >= 0)) (PreH12 : (gcap <= INT_MAX)) (PreH13 : ((Zabs (gsize)) <= gcap)) (PreH14 : (same_sign old gsize )) (PreH15 : (0 <= rem)) (PreH16 : (rem <= UINT_MAX)) (PreH17 : (0 <= tv_val)) (PreH18 : (tv_val <= UINT_MAX)) (PreH19 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH20 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH21 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH22 : ((Zlength (vdata)) = 1)) (PreH23 : ((last (tdata) (1)) >= 1)) (PreH24 : (list_within_bound UINT_MOD tdata )) (PreH25 : (list_within_bound UINT_MOD vdata )) (PreH26 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH27 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH28 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH29 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH30 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |-> retval)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (same_sign tv_final vsize ) ” 
  &&  “ ((Zabs (vsize)) <= vcap) ” 
  &&  “ (same_sign tu_final tsize ) ” 
  &&  “ ((Zabs (tsize)) <= tcap) ” 
  &&  “ (same_sign g_odd 0 ) ” 
  &&  “ ((Zabs (0)) <= g__mp_alloc) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (tv_final)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg tptr (Zabs (tsize)) tcap )
  **  (mpd_store_Z_compact UINT_MOD tptr (Zabs (tu_final)) (Zabs (tsize)) )
  **  (UIntArray.undef_seg g__mp_d (Zabs (0)) g__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD g__mp_d (Zabs (g_odd)) (Zabs (0)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_entail_wit_9_7 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zgcd ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0))))) (PreH3 : (tu <> 0)) (PreH4 : (tv <> 0)) (PreH5 : (gp = g__mp_d)) (PreH6 : (gz_v >= 0)) (PreH7 : (tv_val > 0)) (PreH8 : (vsize = 1)) (PreH9 : (gcap >= 0)) (PreH10 : (gcap <= INT_MAX)) (PreH11 : ((Zabs (gsize)) <= gcap)) (PreH12 : (same_sign old gsize )) (PreH13 : (0 <= rem)) (PreH14 : (rem <= UINT_MAX)) (PreH15 : (0 <= tv_val)) (PreH16 : (tv_val <= UINT_MAX)) (PreH17 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH18 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH19 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH20 : ((Zlength (vdata)) = 1)) (PreH21 : ((last (tdata) (1)) >= 1)) (PreH22 : (list_within_bound UINT_MOD tdata )) (PreH23 : (list_within_bound UINT_MOD vdata )) (PreH24 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH25 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH26 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH27 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH28 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |-> retval)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z tu tu_final )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval = (Zgcd ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0))))) (PreH5 : (tu <> 0)) (PreH6 : (tv <> 0)) (PreH7 : (gp = g__mp_d)) (PreH8 : (gz_v >= 0)) (PreH9 : (tv_val > 0)) (PreH10 : (vsize = 1)) (PreH11 : (gcap >= 0)) (PreH12 : (gcap <= INT_MAX)) (PreH13 : ((Zabs (gsize)) <= gcap)) (PreH14 : (same_sign old gsize )) (PreH15 : (0 <= rem)) (PreH16 : (rem <= UINT_MAX)) (PreH17 : (0 <= tv_val)) (PreH18 : (tv_val <= UINT_MAX)) (PreH19 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH20 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH21 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH22 : ((Zlength (vdata)) = 1)) (PreH23 : ((last (tdata) (1)) >= 1)) (PreH24 : (list_within_bound UINT_MOD tdata )) (PreH25 : (list_within_bound UINT_MOD vdata )) (PreH26 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH27 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH28 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH29 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH30 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |-> retval)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (tv_final: Z)  (tu_final: Z)  (g_odd: Z) ,
  “ (same_sign tv_final vsize ) ” 
  &&  “ ((Zabs (vsize)) <= vcap) ” 
  &&  “ (same_sign tu_final tsize ) ” 
  &&  “ ((Zabs (tsize)) <= tcap) ” 
  &&  “ (same_sign g_odd 1 ) ” 
  &&  “ ((Zabs (1)) <= g__mp_alloc) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (tv_final)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg tptr (Zabs (tsize)) tcap )
  **  (mpd_store_Z_compact UINT_MOD tptr (Zabs (tu_final)) (Zabs (tsize)) )
  **  (UIntArray.undef_seg g__mp_d (Zabs (1)) g__mp_alloc )
  **  (mpd_store_Z_compact UINT_MOD g__mp_d (Zabs (g_odd)) (Zabs (1)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_return_wit_1 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (store_Z g_pre (Zabs (zu)) )
  **  (store_Z u_pre zu )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
|--
  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (store_Z g_pre (Zabs (zu)) )
  **  (store_Z u_pre zu )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
  **  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
).

Definition mpz_gcd_return_wit_1_split_goal_spatial := 
forall (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  (store_Z g_pre (Zabs (zu)) )
  **  (store_Z u_pre zu )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
  **  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
.

Definition mpz_gcd_return_wit_2 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign zu size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  (store_Z g_pre (Zabs (zv)) )
  **  (store_Z v_pre zv )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign zu size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  (store_Z g_pre (Zabs (zv)) )
  **  (store_Z v_pre zv )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_return_wit_2_split_goal_spatial := 
forall (v_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign zu size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  (store_Z g_pre (Zabs (zv)) )
  **  (store_Z v_pre zv )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_return_wit_3 := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (g_pre = g_pre)) (PreH2 : (tu <> 0)) (PreH3 : (tv <> 0)) (PreH4 : (gz_v >= 0)) (PreH5 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH6 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  (store_Z g_pre (g_odd * (Z.pow (2) (gz_v)) ) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  (store_Z g_pre (g_odd * (Z.pow (2) (gz_v)) ) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
).

Definition mpz_gcd_return_wit_3_split_goal_spatial := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  (store_Z g_pre (g_odd * (Z.pow (2) (gz_v)) ) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  (store_Z g_pre (Zgcd (zu) (zv)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) ,
  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign zu size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign zu size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
|--
  “ (size = 0) ” 
  &&  “ (same_sign zu size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z g_pre old )
  **  (store_Z v_pre zv )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_gcd_partial_solve_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign zu size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign zv size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign zu size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zv)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_4 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (ptr_2: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign zv size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign zu size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zu)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z g_pre old )
|--
  “ (size_2 = 0) ” 
  &&  “ (same_sign zv size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (size <> 0) ” 
  &&  “ (same_sign zu size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (zv)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
.

Definition mpz_gcd_partial_solve_wit_5 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (PreH1 : ((Zabs (zu)) > 0)) (PreH2 : ((Zabs (zv)) > 0)) (PreH3 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_6 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Zabs (zu)) > 0)) (PreH3 : ((Zabs (zv)) > 0)) (PreH4 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_7 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : ((Zabs (zu)) > 0)) (PreH4 : ((Zabs (zv)) > 0)) (PreH5 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_8 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : ((Zabs (zu)) > 0)) (PreH4 : ((Zabs (zv)) > 0)) (PreH5 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval 0 )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_9 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : ((Zabs (zu)) > 0)) (PreH4 : ((Zabs (zv)) > 0)) (PreH5 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval 0 )
  **  (store_Z u_pre zu )
  **  (store_Z retval_2 0 )
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_10_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : ((Zabs (zu)) > 0)) (PreH4 : ((Zabs (zv)) > 0)) (PreH5 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval (Zabs (zu)) )
  **  (store_Z u_pre zu )
  **  (store_Z retval_2 0 )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |->_)
  **  ((( &( "vz" ) )) # UInt64  |->_)
  **  ((( &( "gz" ) )) # UInt64  |->_)
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
|--
  “ ((Zabs (zu)) > 0) ”
.

Definition mpz_gcd_partial_solve_wit_10_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : ((Zabs (zu)) > 0)) (PreH4 : ((Zabs (zv)) > 0)) (PreH5 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval (Zabs (zu)) )
  **  (store_Z u_pre zu )
  **  (store_Z retval_2 0 )
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
|--
  “ ((Zabs (zu)) > 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval (Zabs (zu)) )
  **  (store_Z u_pre zu )
  **  (store_Z retval_2 0 )
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_10 := mpz_gcd_partial_solve_wit_10_pure -> mpz_gcd_partial_solve_wit_10_aux.

Definition mpz_gcd_partial_solve_wit_11 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (odd > 0)) (PreH3 : ((odd % ( 2 ) ) = 1)) (PreH4 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : ((Zabs (zu)) > 0)) (PreH8 : ((Zabs (zv)) > 0)) (PreH9 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  (store_Z retval_2 0 )
  **  (store_Z g_pre old )
  **  (store_Z v_pre zv )
|--
  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z v_pre zv )
  **  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_12_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (odd > 0)) (PreH3 : ((odd % ( 2 ) ) = 1)) (PreH4 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : ((Zabs (zu)) > 0)) (PreH8 : ((Zabs (zv)) > 0)) (PreH9 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval_2 (Zabs (zv)) )
  **  (store_Z v_pre zv )
  **  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |->_)
  **  ((( &( "gz" ) )) # UInt64  |->_)
  **  (store_Z g_pre old )
|--
  “ ((Zabs (zv)) > 0) ”
.

Definition mpz_gcd_partial_solve_wit_12_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (odd > 0)) (PreH3 : ((odd % ( 2 ) ) = 1)) (PreH4 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : ((Zabs (zu)) > 0)) (PreH8 : ((Zabs (zv)) > 0)) (PreH9 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval_2 (Zabs (zv)) )
  **  (store_Z v_pre zv )
  **  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ ((Zabs (zv)) > 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval_2 (Zabs (zv)) )
  **  (store_Z v_pre zv )
  **  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_12 := mpz_gcd_partial_solve_wit_12_pure -> mpz_gcd_partial_solve_wit_12_aux.

Definition mpz_gcd_partial_solve_wit_13 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (PreH1 : (retval_3 < retval_4)) (PreH2 : (0 <= retval_4)) (PreH3 : (odd_2 > 0)) (PreH4 : ((odd_2 % ( 2 ) ) = 1)) (PreH5 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH6 : (0 <= retval_3)) (PreH7 : (odd > 0)) (PreH8 : ((odd % ( 2 ) ) = 1)) (PreH9 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval <> 0)) (PreH12 : ((Zabs (zu)) > 0)) (PreH13 : ((Zabs (zv)) > 0)) (PreH14 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_14 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (PreH1 : (retval_3 >= retval_4)) (PreH2 : (0 <= retval_4)) (PreH3 : (odd_2 > 0)) (PreH4 : ((odd_2 % ( 2 ) ) = 1)) (PreH5 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH6 : (0 <= retval_3)) (PreH7 : (odd > 0)) (PreH8 : ((odd % ( 2 ) ) = 1)) (PreH9 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval <> 0)) (PreH12 : ((Zabs (zu)) > 0)) (PreH13 : ((Zabs (zv)) > 0)) (PreH14 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z retval odd )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_15 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign odd size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (retval_3 < retval_4)) (PreH4 : (0 <= retval_4)) (PreH5 : (odd_2 > 0)) (PreH6 : ((odd_2 % ( 2 ) ) = 1)) (PreH7 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH8 : (0 <= retval_3)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval <> 0)) (PreH14 : ((Zabs (zu)) > 0)) (PreH15 : ((Zabs (zv)) > 0)) (PreH16 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_16 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign odd size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (retval_3 >= retval_4)) (PreH4 : (0 <= retval_4)) (PreH5 : (odd_2 > 0)) (PreH6 : ((odd_2 % ( 2 ) ) = 1)) (PreH7 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH8 : (0 <= retval_3)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval <> 0)) (PreH14 : ((Zabs (zu)) > 0)) (PreH15 : ((Zabs (zv)) > 0)) (PreH16 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_17 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 < retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval odd )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_18 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 >= retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval odd )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_19_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 < retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval odd_2 )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_3)
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd_2 <> 0) ” 
  &&  “ (odd <> 0) ”
.

Definition mpz_gcd_partial_solve_wit_19_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 < retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval odd_2 )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd_2 <> 0) ” 
  &&  “ (odd <> 0) ” 
  &&  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval odd_2 )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_19 := mpz_gcd_partial_solve_wit_19_pure -> mpz_gcd_partial_solve_wit_19_aux.

Definition mpz_gcd_partial_solve_wit_20_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 >= retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval odd_2 )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_4)
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd_2 <> 0) ” 
  &&  “ (odd <> 0) ”
.

Definition mpz_gcd_partial_solve_wit_20_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size < size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 >= retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z retval odd_2 )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd_2 <> 0) ” 
  &&  “ (odd <> 0) ” 
  &&  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval odd_2 )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_20 := mpz_gcd_partial_solve_wit_20_pure -> mpz_gcd_partial_solve_wit_20_aux.

Definition mpz_gcd_partial_solve_wit_21_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size >= size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 < retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_3)
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd <> 0) ” 
  &&  “ (odd_2 <> 0) ”
.

Definition mpz_gcd_partial_solve_wit_21_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size >= size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 < retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd <> 0) ” 
  &&  “ (odd_2 <> 0) ” 
  &&  “ (size >= size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval odd )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_21 := mpz_gcd_partial_solve_wit_21_pure -> mpz_gcd_partial_solve_wit_21_aux.

Definition mpz_gcd_partial_solve_wit_22_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size >= size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 >= retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> retval)
  **  ((( &( "tv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "uz" ) )) # UInt64  |-> retval_3)
  **  ((( &( "vz" ) )) # UInt64  |-> retval_4)
  **  ((( &( "gz" ) )) # UInt64  |-> retval_4)
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd <> 0) ” 
  &&  “ (odd_2 <> 0) ”
.

Definition mpz_gcd_partial_solve_wit_22_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size >= size_2)) (PreH2 : (same_sign odd_2 size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign odd size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (retval_3 >= retval_4)) (PreH7 : (0 <= retval_4)) (PreH8 : (odd_2 > 0)) (PreH9 : ((odd_2 % ( 2 ) ) = 1)) (PreH10 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH11 : (0 <= retval_3)) (PreH12 : (odd > 0)) (PreH13 : ((odd % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH15 : (retval_2 <> 0)) (PreH16 : (retval <> 0)) (PreH17 : ((Zabs (zu)) > 0)) (PreH18 : ((Zabs (zv)) > 0)) (PreH19 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (odd_2)) (Zabs (size_2)) )
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (retval = retval) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (odd <> 0) ” 
  &&  “ (odd_2 <> 0) ” 
  &&  “ (size >= size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z retval odd )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_22 := mpz_gcd_partial_solve_wit_22_pure -> mpz_gcd_partial_solve_wit_22_aux.

Definition mpz_gcd_partial_solve_wit_23 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (PreH1 : (retval = retval)) (PreH2 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH3 : (size < size_2)) (PreH4 : (same_sign odd_2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign odd size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (retval_3 < retval_4)) (PreH9 : (0 <= retval_4)) (PreH10 : (odd_2 > 0)) (PreH11 : ((odd_2 % ( 2 ) ) = 1)) (PreH12 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH13 : (0 <= retval_3)) (PreH14 : (odd > 0)) (PreH15 : ((odd % ( 2 ) ) = 1)) (PreH16 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval <> 0)) (PreH19 : ((Zabs (zu)) > 0)) (PreH20 : ((Zabs (zv)) > 0)) (PreH21 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z_read0 retval rv )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd_2 odd qv rv ) ” 
  &&  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_24 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (PreH1 : (retval = retval)) (PreH2 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH3 : (size < size_2)) (PreH4 : (same_sign odd_2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign odd size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (retval_3 >= retval_4)) (PreH9 : (0 <= retval_4)) (PreH10 : (odd_2 > 0)) (PreH11 : ((odd_2 % ( 2 ) ) = 1)) (PreH12 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH13 : (0 <= retval_3)) (PreH14 : (odd > 0)) (PreH15 : ((odd % ( 2 ) ) = 1)) (PreH16 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval <> 0)) (PreH19 : ((Zabs (zu)) > 0)) (PreH20 : ((Zabs (zv)) > 0)) (PreH21 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z_read0 retval rv )
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd_2 odd qv rv ) ” 
  &&  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_25 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (PreH1 : (retval = retval)) (PreH2 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH3 : (size >= size_2)) (PreH4 : (same_sign odd_2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign odd size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (retval_3 < retval_4)) (PreH9 : (0 <= retval_4)) (PreH10 : (odd_2 > 0)) (PreH11 : ((odd_2 % ( 2 ) ) = 1)) (PreH12 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH13 : (0 <= retval_3)) (PreH14 : (odd > 0)) (PreH15 : ((odd % ( 2 ) ) = 1)) (PreH16 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval <> 0)) (PreH19 : ((Zabs (zu)) > 0)) (PreH20 : ((Zabs (zv)) > 0)) (PreH21 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z_read0 retval rv )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd odd_2 qv rv ) ” 
  &&  “ (size >= size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_26 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (PreH1 : (retval = retval)) (PreH2 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH3 : (size >= size_2)) (PreH4 : (same_sign odd_2 size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign odd size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (retval_3 >= retval_4)) (PreH9 : (0 <= retval_4)) (PreH10 : (odd_2 > 0)) (PreH11 : ((odd_2 % ( 2 ) ) = 1)) (PreH12 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH13 : (0 <= retval_3)) (PreH14 : (odd > 0)) (PreH15 : ((odd % ( 2 ) ) = 1)) (PreH16 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval <> 0)) (PreH19 : ((Zabs (zu)) > 0)) (PreH20 : ((Zabs (zv)) > 0)) (PreH21 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  (store_Z_read0 retval rv )
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd odd_2 qv rv ) ” 
  &&  “ (size >= size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
.

Definition mpz_gcd_partial_solve_wit_27 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (size_3 = 0) ” 
  &&  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd_2 odd qv rv ) ” 
  &&  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z g_pre old )
  **  (store_Z retval_2 odd )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
.

Definition mpz_gcd_partial_solve_wit_28 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd_2 odd qv rv )) (PreH5 : (size < size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 >= retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (size_3 = 0) ” 
  &&  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd_2 odd qv rv ) ” 
  &&  “ (size < size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z g_pre old )
  **  (store_Z retval_2 odd )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
.

Definition mpz_gcd_partial_solve_wit_29 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 < retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (size_3 = 0) ” 
  &&  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd odd_2 qv rv ) ” 
  &&  “ (size >= size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 < retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z g_pre old )
  **  (store_Z retval_2 odd_2 )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
.

Definition mpz_gcd_partial_solve_wit_30 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (retval: Z) (retval_2: Z) (odd: Z) (retval_3: Z) (odd_2: Z) (retval_4: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (qv: Z) (rv: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 = 0)) (PreH2 : (same_sign rv size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : (mpz_div_qr_math 2 odd odd_2 qv rv )) (PreH5 : (size >= size_2)) (PreH6 : (same_sign odd_2 size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (same_sign odd size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (retval_3 >= retval_4)) (PreH11 : (0 <= retval_4)) (PreH12 : (odd_2 > 0)) (PreH13 : ((odd_2 % ( 2 ) ) = 1)) (PreH14 : ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) ))) (PreH15 : (0 <= retval_3)) (PreH16 : (odd > 0)) (PreH17 : ((odd % ( 2 ) ) = 1)) (PreH18 : ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) ))) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval <> 0)) (PreH21 : ((Zabs (zu)) > 0)) (PreH22 : ((Zabs (zv)) > 0)) (PreH23 : (mpz_one_limb_headroom (Zgcd (zu) (zv)) )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z retval_2 odd_2 )
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
  **  (store_Z g_pre old )
|--
  “ (size_3 = 0) ” 
  &&  “ (same_sign rv size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (mpz_div_qr_math 2 odd odd_2 qv rv ) ” 
  &&  “ (size >= size_2) ” 
  &&  “ (same_sign odd_2 size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_3 >= retval_4) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (odd_2 > 0) ” 
  &&  “ ((odd_2 % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zv)) = (odd_2 * (Z.pow (2) (retval_4)) )) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ ((Zabs (zu)) = (odd * (Z.pow (2) (retval_3)) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Zabs (zu)) > 0) ” 
  &&  “ ((Zabs (zv)) > 0) ” 
  &&  “ (mpz_one_limb_headroom (Zgcd (zu) (zv)) ) ”
  &&  (store_Z g_pre old )
  **  (store_Z retval_2 odd_2 )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size_3))) (1)) cap_3 )
  **  (mpd_store_Z_compact_read0 ptr (Zabs (rv)) (Zabs (size_3)) )
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z v_pre zv )
  **  (store_Z u_pre zu )
.

Definition mpz_gcd_partial_solve_wit_31_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (tu_v > 0)) (PreH5 : (tv_v > 0)) (PreH6 : ((tv_v % ( 2 ) ) = 1)) (PreH7 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH8 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu_v > 0) ”
.

Definition mpz_gcd_partial_solve_wit_31_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (tu_v > 0)) (PreH5 : (tv_v > 0)) (PreH6 : ((tv_v % ( 2 ) ) = 1)) (PreH7 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH8 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu_v > 0) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_31 := mpz_gcd_partial_solve_wit_31_pure -> mpz_gcd_partial_solve_wit_31_aux.

Definition mpz_gcd_partial_solve_wit_32 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (odd > 0)) (PreH3 : ((odd % ( 2 ) ) = 1)) (PreH4 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH5 : (tu <> 0)) (PreH6 : (tv <> 0)) (PreH7 : (gz_v >= 0)) (PreH8 : (tu_v > 0)) (PreH9 : (tv_v > 0)) (PreH10 : ((tv_v % ( 2 ) ) = 1)) (PreH11 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH12 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_33 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (odd = tv_v)) (PreH3 : (retval_2 = 0)) (PreH4 : (0 <= retval)) (PreH5 : (odd > 0)) (PreH6 : ((odd % ( 2 ) ) = 1)) (PreH7 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH8 : (tu <> 0)) (PreH9 : (tv <> 0)) (PreH10 : (gz_v >= 0)) (PreH11 : (tu_v > 0)) (PreH12 : (tv_v > 0)) (PreH13 : ((tv_v % ( 2 ) ) = 1)) (PreH14 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH15 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (retval_2 = 0) ” 
  &&  “ (odd = tv_v) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z g_pre old )
  **  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_34 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (odd < tv_v)) (PreH4 : (retval_2 = (-1))) (PreH5 : (0 <= retval)) (PreH6 : (odd > 0)) (PreH7 : ((odd % ( 2 ) ) = 1)) (PreH8 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH9 : (tu <> 0)) (PreH10 : (tv <> 0)) (PreH11 : (gz_v >= 0)) (PreH12 : (tu_v > 0)) (PreH13 : (tv_v > 0)) (PreH14 : ((tv_v % ( 2 ) ) = 1)) (PreH15 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH16 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (odd < tv_v) ” 
  &&  “ (retval_2 = (-1)) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_35 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (odd < tv_v)) (PreH4 : (retval_2 = (-1))) (PreH5 : (0 <= retval)) (PreH6 : (odd > 0)) (PreH7 : ((odd % ( 2 ) ) = 1)) (PreH8 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH9 : (tu <> 0)) (PreH10 : (tv <> 0)) (PreH11 : (gz_v >= 0)) (PreH12 : (tu_v > 0)) (PreH13 : (tv_v > 0)) (PreH14 : ((tv_v % ( 2 ) ) = 1)) (PreH15 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH16 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu tv_v )
  **  (store_Z tv odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (odd < tv_v) ” 
  &&  “ (retval_2 = (-1)) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_36 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (odd > tv_v)) (PreH4 : (retval_2 = 1)) (PreH5 : (0 <= retval)) (PreH6 : (odd > 0)) (PreH7 : ((odd % ( 2 ) ) = 1)) (PreH8 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH9 : (tu <> 0)) (PreH10 : (tv <> 0)) (PreH11 : (gz_v >= 0)) (PreH12 : (tu_v > 0)) (PreH13 : (tv_v > 0)) (PreH14 : ((tv_v % ( 2 ) ) = 1)) (PreH15 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH16 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign tv_v size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (odd > tv_v) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_37_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (cval: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (tu_v > 0)) (PreH5 : (tv_v > 0)) (PreH6 : (tv_v <= UINT_MAX)) (PreH7 : ((tv_v % ( 2 ) ) = 1)) (PreH8 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH9 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((( &( "gp" ) )) # Ptr  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu = tu) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tu_v <> 0) ” 
  &&  “ (tv_v <> 0) ”
.

Definition mpz_gcd_partial_solve_wit_37_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (tu_v > 0)) (PreH5 : (tv_v > 0)) (PreH6 : (tv_v <= UINT_MAX)) (PreH7 : ((tv_v % ( 2 ) ) = 1)) (PreH8 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH9 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu = tu) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tu_v <> 0) ” 
  &&  “ (tv_v <> 0) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tu_v )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_37 := mpz_gcd_partial_solve_wit_37_pure -> mpz_gcd_partial_solve_wit_37_aux.

Definition mpz_gcd_partial_solve_wit_38_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (cval: Z) (qv: Z) (rv: Z) (gptr: Z) (gsize: Z) (gcap: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (mpz_div_qr_math 2 tu_v tv_v qv rv )) (PreH4 : (gz_v >= 0)) (PreH5 : (tu_v > 0)) (PreH6 : (tv_v > 0)) (PreH7 : (tv_v <= UINT_MAX)) (PreH8 : ((tv_v % ( 2 ) ) = 1)) (PreH9 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH10 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) (PreH11 : (gcap >= 0)) (PreH12 : (gcap <= INT_MAX)) (PreH13 : ((Zabs (gsize)) <= gcap)) (PreH14 : (same_sign old gsize )) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> gptr)
  **  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  ((( &( "gp" ) )) # Ptr  |->_)
  **  (mpd_store_Z_compact UINT_MOD gptr (Zabs (old)) (Zabs (gsize)) )
  **  (UIntArray.undef_seg gptr (Zabs (gsize)) gcap )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ”
.

Definition mpz_gcd_partial_solve_wit_38_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tu_v: Z) (tv_v: Z) (gz_v: Z) (qv: Z) (rv: Z) (gptr: Z) (gsize: Z) (gcap: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (mpz_div_qr_math 2 tu_v tv_v qv rv )) (PreH4 : (gz_v >= 0)) (PreH5 : (tu_v > 0)) (PreH6 : (tv_v > 0)) (PreH7 : (tv_v <= UINT_MAX)) (PreH8 : ((tv_v % ( 2 ) ) = 1)) (PreH9 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH10 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) (PreH11 : (gcap >= 0)) (PreH12 : (gcap <= INT_MAX)) (PreH13 : ((Zabs (gsize)) <= gcap)) (PreH14 : (same_sign old gsize )) ,
  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> gptr)
  **  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  (mpd_store_Z_compact UINT_MOD gptr (Zabs (old)) (Zabs (gsize)) )
  **  (UIntArray.undef_seg gptr (Zabs (gsize)) gcap )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (mpz_div_qr_math 2 tu_v tv_v qv rv ) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ (tv_v <= UINT_MAX) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ”
  &&  (mpd_store_Z_compact UINT_MOD gptr (Zabs (old)) (Zabs (gsize)) )
  **  (UIntArray.undef_seg gptr (Zabs (gsize)) gcap )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> gptr)
  **  (store_Z_read0 tu rv )
  **  (store_Z tv tv_v )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_38 := mpz_gcd_partial_solve_wit_38_pure -> mpz_gcd_partial_solve_wit_38_aux.

Definition mpz_gcd_partial_solve_wit_39 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val > 0)) (PreH6 : (vsize = 1)) (PreH7 : (gcap >= 0)) (PreH8 : (gcap <= INT_MAX)) (PreH9 : ((Zabs (gsize)) <= gcap)) (PreH10 : (same_sign old gsize )) (PreH11 : (0 <= rem)) (PreH12 : (rem <= UINT_MAX)) (PreH13 : (0 <= tv_val)) (PreH14 : (tv_val <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH16 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH17 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH18 : ((Zlength (vdata)) = 1)) (PreH19 : ((last (tdata) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata )) (PreH21 : (list_within_bound UINT_MOD vdata )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH26 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gp = g__mp_d) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tv_val > 0) ” 
  &&  “ (vsize = 1) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ” 
  &&  “ (0 <= rem) ” 
  &&  “ (rem <= UINT_MAX) ” 
  &&  “ (0 <= tv_val) ” 
  &&  “ (tv_val <= UINT_MAX) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem) ” 
  &&  “ ((Znth (0) (vdata) (0)) = tv_val) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (tsize))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = rem) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = tv_val) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) )) ” 
  &&  “ (g__mp_alloc = (Z.max (1) (gcap))) ”
  &&  (((tptr + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0))
  **  (UIntArray.missing_i tptr 0 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_40 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val > 0)) (PreH6 : (vsize = 1)) (PreH7 : (gcap >= 0)) (PreH8 : (gcap <= INT_MAX)) (PreH9 : ((Zabs (gsize)) <= gcap)) (PreH10 : (same_sign old gsize )) (PreH11 : (0 <= rem)) (PreH12 : (rem <= UINT_MAX)) (PreH13 : (0 <= tv_val)) (PreH14 : (tv_val <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH16 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH17 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH18 : ((Zlength (vdata)) = 1)) (PreH19 : ((last (tdata) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata )) (PreH21 : (list_within_bound UINT_MOD vdata )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH26 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gp = g__mp_d) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tv_val > 0) ” 
  &&  “ (vsize = 1) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ” 
  &&  “ (0 <= rem) ” 
  &&  “ (rem <= UINT_MAX) ” 
  &&  “ (0 <= tv_val) ” 
  &&  “ (tv_val <= UINT_MAX) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem) ” 
  &&  “ ((Znth (0) (vdata) (0)) = tv_val) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (tsize))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = rem) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = tv_val) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) )) ” 
  &&  “ (g__mp_alloc = (Z.max (1) (gcap))) ”
  &&  (((vptr + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0))
  **  (UIntArray.missing_i vptr 0 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_41_pure := 
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val > 0)) (PreH6 : (vsize = 1)) (PreH7 : (gcap >= 0)) (PreH8 : (gcap <= INT_MAX)) (PreH9 : ((Zabs (gsize)) <= gcap)) (PreH10 : (same_sign old gsize )) (PreH11 : (0 <= rem)) (PreH12 : (rem <= UINT_MAX)) (PreH13 : (0 <= tv_val)) (PreH14 : (tv_val <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH16 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH17 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH18 : ((Zlength (vdata)) = 1)) (PreH19 : ((last (tdata) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata )) (PreH21 : (list_within_bound UINT_MOD vdata )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH26 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) + (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) ) > 0) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0)) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ”
) \/
(
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (g__mp_alloc <= INT_MAX)) (PreH2 : (gsize <= INT_MAX)) (PreH3 : (vcap <= INT_MAX)) (PreH4 : (vsize <= INT_MAX)) (PreH5 : (tcap <= INT_MAX)) (PreH6 : (tsize <= INT_MAX)) (PreH7 : (cval <= INT_MAX)) (PreH8 : (g__mp_alloc >= INT_MIN)) (PreH9 : (gsize >= INT_MIN)) (PreH10 : (vcap >= INT_MIN)) (PreH11 : (vsize >= INT_MIN)) (PreH12 : (tcap >= INT_MIN)) (PreH13 : (tsize >= INT_MIN)) (PreH14 : (cval >= INT_MIN)) (PreH15 : (tu <> 0)) (PreH16 : (tv <> 0)) (PreH17 : (gp = g__mp_d)) (PreH18 : (gz_v >= 0)) (PreH19 : (tv_val > 0)) (PreH20 : (vsize = 1)) (PreH21 : (gcap >= 0)) (PreH22 : (gcap <= INT_MAX)) (PreH23 : ((Zabs (gsize)) <= gcap)) (PreH24 : (same_sign old gsize )) (PreH25 : (0 <= rem)) (PreH26 : (rem <= UINT_MAX)) (PreH27 : (0 <= tv_val)) (PreH28 : (tv_val <= UINT_MAX)) (PreH29 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH30 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH31 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH32 : ((Zlength (vdata)) = 1)) (PreH33 : ((last (tdata) (1)) >= 1)) (PreH34 : (list_within_bound UINT_MOD tdata )) (PreH35 : (list_within_bound UINT_MOD vdata )) (PreH36 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH37 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH38 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH39 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH40 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0)) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) <= UINT_MAX) ” 
  &&  “ (((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) + (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) ) > 0) ”
).

Definition mpz_gcd_partial_solve_wit_41_pure_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (g__mp_alloc <= INT_MAX)) (PreH2 : (gsize <= INT_MAX)) (PreH3 : (vcap <= INT_MAX)) (PreH4 : (vsize <= INT_MAX)) (PreH5 : (tcap <= INT_MAX)) (PreH6 : (tsize <= INT_MAX)) (PreH7 : (cval <= INT_MAX)) (PreH8 : (g__mp_alloc >= INT_MIN)) (PreH9 : (gsize >= INT_MIN)) (PreH10 : (vcap >= INT_MIN)) (PreH11 : (vsize >= INT_MIN)) (PreH12 : (tcap >= INT_MIN)) (PreH13 : (tsize >= INT_MIN)) (PreH14 : (cval >= INT_MIN)) (PreH15 : (tu <> 0)) (PreH16 : (tv <> 0)) (PreH17 : (gp = g__mp_d)) (PreH18 : (gz_v >= 0)) (PreH19 : (tv_val > 0)) (PreH20 : (vsize = 1)) (PreH21 : (gcap >= 0)) (PreH22 : (gcap <= INT_MAX)) (PreH23 : ((Zabs (gsize)) <= gcap)) (PreH24 : (same_sign old gsize )) (PreH25 : (0 <= rem)) (PreH26 : (rem <= UINT_MAX)) (PreH27 : (0 <= tv_val)) (PreH28 : (tv_val <= UINT_MAX)) (PreH29 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH30 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH31 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH32 : ((Zlength (vdata)) = 1)) (PreH33 : ((last (tdata) (1)) >= 1)) (PreH34 : (list_within_bound UINT_MOD tdata )) (PreH35 : (list_within_bound UINT_MOD vdata )) (PreH36 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH37 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH38 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH39 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH40 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ”
.

Definition mpz_gcd_partial_solve_wit_41_pure_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (g__mp_alloc <= INT_MAX)) (PreH2 : (gsize <= INT_MAX)) (PreH3 : (vcap <= INT_MAX)) (PreH4 : (vsize <= INT_MAX)) (PreH5 : (tcap <= INT_MAX)) (PreH6 : (tsize <= INT_MAX)) (PreH7 : (cval <= INT_MAX)) (PreH8 : (g__mp_alloc >= INT_MIN)) (PreH9 : (gsize >= INT_MIN)) (PreH10 : (vcap >= INT_MIN)) (PreH11 : (vsize >= INT_MIN)) (PreH12 : (tcap >= INT_MIN)) (PreH13 : (tsize >= INT_MIN)) (PreH14 : (cval >= INT_MIN)) (PreH15 : (tu <> 0)) (PreH16 : (tv <> 0)) (PreH17 : (gp = g__mp_d)) (PreH18 : (gz_v >= 0)) (PreH19 : (tv_val > 0)) (PreH20 : (vsize = 1)) (PreH21 : (gcap >= 0)) (PreH22 : (gcap <= INT_MAX)) (PreH23 : ((Zabs (gsize)) <= gcap)) (PreH24 : (same_sign old gsize )) (PreH25 : (0 <= rem)) (PreH26 : (rem <= UINT_MAX)) (PreH27 : (0 <= tv_val)) (PreH28 : (tv_val <= UINT_MAX)) (PreH29 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH30 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH31 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH32 : ((Zlength (vdata)) = 1)) (PreH33 : ((last (tdata) (1)) >= 1)) (PreH34 : (list_within_bound UINT_MOD tdata )) (PreH35 : (list_within_bound UINT_MOD vdata )) (PreH36 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH37 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH38 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH39 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH40 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) <= UINT_MAX) ”
.

Definition mpz_gcd_partial_solve_wit_41_pure_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (g__mp_alloc <= INT_MAX)) (PreH2 : (gsize <= INT_MAX)) (PreH3 : (vcap <= INT_MAX)) (PreH4 : (vsize <= INT_MAX)) (PreH5 : (tcap <= INT_MAX)) (PreH6 : (tsize <= INT_MAX)) (PreH7 : (cval <= INT_MAX)) (PreH8 : (g__mp_alloc >= INT_MIN)) (PreH9 : (gsize >= INT_MIN)) (PreH10 : (vcap >= INT_MIN)) (PreH11 : (vsize >= INT_MIN)) (PreH12 : (tcap >= INT_MIN)) (PreH13 : (tsize >= INT_MIN)) (PreH14 : (cval >= INT_MIN)) (PreH15 : (tu <> 0)) (PreH16 : (tv <> 0)) (PreH17 : (gp = g__mp_d)) (PreH18 : (gz_v >= 0)) (PreH19 : (tv_val > 0)) (PreH20 : (vsize = 1)) (PreH21 : (gcap >= 0)) (PreH22 : (gcap <= INT_MAX)) (PreH23 : ((Zabs (gsize)) <= gcap)) (PreH24 : (same_sign old gsize )) (PreH25 : (0 <= rem)) (PreH26 : (rem <= UINT_MAX)) (PreH27 : (0 <= tv_val)) (PreH28 : (tv_val <= UINT_MAX)) (PreH29 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH30 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH31 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH32 : ((Zlength (vdata)) = 1)) (PreH33 : ((last (tdata) (1)) >= 1)) (PreH34 : (list_within_bound UINT_MOD tdata )) (PreH35 : (list_within_bound UINT_MOD vdata )) (PreH36 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH37 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH38 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH39 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH40 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0)) ”
.

Definition mpz_gcd_partial_solve_wit_41_pure_split_goal_4 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (g__mp_alloc <= INT_MAX)) (PreH2 : (gsize <= INT_MAX)) (PreH3 : (vcap <= INT_MAX)) (PreH4 : (vsize <= INT_MAX)) (PreH5 : (tcap <= INT_MAX)) (PreH6 : (tsize <= INT_MAX)) (PreH7 : (cval <= INT_MAX)) (PreH8 : (g__mp_alloc >= INT_MIN)) (PreH9 : (gsize >= INT_MIN)) (PreH10 : (vcap >= INT_MIN)) (PreH11 : (vsize >= INT_MIN)) (PreH12 : (tcap >= INT_MIN)) (PreH13 : (tsize >= INT_MIN)) (PreH14 : (cval >= INT_MIN)) (PreH15 : (tu <> 0)) (PreH16 : (tv <> 0)) (PreH17 : (gp = g__mp_d)) (PreH18 : (gz_v >= 0)) (PreH19 : (tv_val > 0)) (PreH20 : (vsize = 1)) (PreH21 : (gcap >= 0)) (PreH22 : (gcap <= INT_MAX)) (PreH23 : ((Zabs (gsize)) <= gcap)) (PreH24 : (same_sign old gsize )) (PreH25 : (0 <= rem)) (PreH26 : (rem <= UINT_MAX)) (PreH27 : (0 <= tv_val)) (PreH28 : (tv_val <= UINT_MAX)) (PreH29 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH30 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH31 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH32 : ((Zlength (vdata)) = 1)) (PreH33 : ((last (tdata) (1)) >= 1)) (PreH34 : (list_within_bound UINT_MOD tdata )) (PreH35 : (list_within_bound UINT_MOD vdata )) (PreH36 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH37 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH38 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH39 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH40 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) <= UINT_MAX) ”
.

Definition mpz_gcd_partial_solve_wit_41_pure_split_goal_5 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (cval: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (g__mp_alloc <= INT_MAX)) (PreH2 : (gsize <= INT_MAX)) (PreH3 : (vcap <= INT_MAX)) (PreH4 : (vsize <= INT_MAX)) (PreH5 : (tcap <= INT_MAX)) (PreH6 : (tsize <= INT_MAX)) (PreH7 : (cval <= INT_MAX)) (PreH8 : (g__mp_alloc >= INT_MIN)) (PreH9 : (gsize >= INT_MIN)) (PreH10 : (vcap >= INT_MIN)) (PreH11 : (vsize >= INT_MIN)) (PreH12 : (tcap >= INT_MIN)) (PreH13 : (tsize >= INT_MIN)) (PreH14 : (cval >= INT_MIN)) (PreH15 : (tu <> 0)) (PreH16 : (tv <> 0)) (PreH17 : (gp = g__mp_d)) (PreH18 : (gz_v >= 0)) (PreH19 : (tv_val > 0)) (PreH20 : (vsize = 1)) (PreH21 : (gcap >= 0)) (PreH22 : (gcap <= INT_MAX)) (PreH23 : ((Zabs (gsize)) <= gcap)) (PreH24 : (same_sign old gsize )) (PreH25 : (0 <= rem)) (PreH26 : (rem <= UINT_MAX)) (PreH27 : (0 <= tv_val)) (PreH28 : (tv_val <= UINT_MAX)) (PreH29 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH30 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH31 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH32 : ((Zlength (vdata)) = 1)) (PreH33 : ((last (tdata) (1)) >= 1)) (PreH34 : (list_within_bound UINT_MOD tdata )) (PreH35 : (list_within_bound UINT_MOD vdata )) (PreH36 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH37 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH38 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH39 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH40 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "c" ) )) # Int  |-> cval)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  ((( &( "gp" ) )) # Ptr  |-> gp)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) + (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) ) > 0) ”
.

Definition mpz_gcd_partial_solve_wit_41_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (rem: Z) (tv_val: Z) (tptr: Z) (tsize: Z) (tcap: Z) (tdata: (@list Z)) (vptr: Z) (vsize: Z) (vcap: Z) (vdata: (@list Z)) (gsize: Z) (gcap: Z) (gz_v: Z) (tu: Z) (tv: Z) (gp: Z) (g__mp_d: Z) (g__mp_alloc: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gp = g__mp_d)) (PreH4 : (gz_v >= 0)) (PreH5 : (tv_val > 0)) (PreH6 : (vsize = 1)) (PreH7 : (gcap >= 0)) (PreH8 : (gcap <= INT_MAX)) (PreH9 : ((Zabs (gsize)) <= gcap)) (PreH10 : (same_sign old gsize )) (PreH11 : (0 <= rem)) (PreH12 : (rem <= UINT_MAX)) (PreH13 : (0 <= tv_val)) (PreH14 : (tv_val <= UINT_MAX)) (PreH15 : ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem)) (PreH16 : ((Znth (0) (vdata) (0)) = tv_val)) (PreH17 : ((Zlength (tdata)) = (Zabs (tsize)))) (PreH18 : ((Zlength (vdata)) = 1)) (PreH19 : ((last (tdata) (1)) >= 1)) (PreH20 : (list_within_bound UINT_MOD tdata )) (PreH21 : (list_within_bound UINT_MOD vdata )) (PreH22 : ((list_to_Z (UINT_MOD) (tdata)) = rem)) (PreH23 : ((list_to_Z (UINT_MOD) (vdata)) = tv_val)) (PreH24 : (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v )) (PreH25 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) ))) (PreH26 : (g__mp_alloc = (Z.max (1) (gcap)))) ,
  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) + (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) ) > 0) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) (vdata)) 0)) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (tdata)))) 0)) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gp = g__mp_d) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tv_val > 0) ” 
  &&  “ (vsize = 1) ” 
  &&  “ (gcap >= 0) ” 
  &&  “ (gcap <= INT_MAX) ” 
  &&  “ ((Zabs (gsize)) <= gcap) ” 
  &&  “ (same_sign old gsize ) ” 
  &&  “ (0 <= rem) ” 
  &&  “ (rem <= UINT_MAX) ” 
  &&  “ (0 <= tv_val) ” 
  &&  “ (tv_val <= UINT_MAX) ” 
  &&  “ ((Znth (0) ((mpd_read0_data (tdata))) (0)) = rem) ” 
  &&  “ ((Znth (0) (vdata) (0)) = tv_val) ” 
  &&  “ ((Zlength (tdata)) = (Zabs (tsize))) ” 
  &&  “ ((Zlength (vdata)) = 1) ” 
  &&  “ ((last (tdata) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD tdata ) ” 
  &&  “ (list_within_bound UINT_MOD vdata ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (tdata)) = rem) ” 
  &&  “ ((list_to_Z (UINT_MOD) (vdata)) = tv_val) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (rem) (tv_val)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (rem) (tv_val)) )) ” 
  &&  “ (g__mp_alloc = (Z.max (1) (gcap))) ”
  &&  (UIntArray.seg vptr 0 1 (sublist (0) (1) (vdata)) )
  **  (UIntArray.seg tptr 0 1 (sublist (0) (1) ((mpd_read0_data (tdata)))) )
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> g__mp_d)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> tsize)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> tcap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> tptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> gsize)
  **  ((&((g_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> g__mp_alloc)
  **  (UIntArray.seg tptr 1 (Zmax ((Zabs (tsize))) (1)) (sublist (1) ((Zmax ((Zabs (tsize))) (1))) ((mpd_read0_data (tdata)))) )
  **  (UIntArray.undef_seg tptr (Zmax ((Zabs (tsize))) (1)) tcap )
  **  (UIntArray.undef_seg vptr 1 vcap )
  **  ((gp) # UInt  |->_)
  **  (UIntArray.undef_seg gp 1 (Z.max (1) (gcap)) )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_41 := mpz_gcd_partial_solve_wit_41_pure -> mpz_gcd_partial_solve_wit_41_aux.

Definition mpz_gcd_partial_solve_wit_42_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign odd size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd < tv_v)) (PreH7 : (retval_2 = (-1))) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v > 0)) (PreH16 : (tv_v > 0)) (PreH17 : ((tv_v % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu tv_v )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu = tu) ”
.

Definition mpz_gcd_partial_solve_wit_42_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign odd size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd < tv_v)) (PreH7 : (retval_2 = (-1))) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v > 0)) (PreH16 : (tv_v > 0)) (PreH17 : ((tv_v % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (odd)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu = tu) ” 
  &&  “ (size <> 1) ” 
  &&  “ (same_sign odd size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (odd < tv_v) ” 
  &&  “ (retval_2 = (-1)) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu tv_v )
  **  (store_Z tv odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_42 := mpz_gcd_partial_solve_wit_42_pure -> mpz_gcd_partial_solve_wit_42_aux.

Definition mpz_gcd_partial_solve_wit_43_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (vz_v: Z) (uz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign tv_v size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd > tv_v)) (PreH7 : (retval_2 = 1)) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v > 0)) (PreH16 : (tv_v > 0)) (PreH17 : ((tv_v % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu odd )
  **  ((( &( "c" ) )) # Int  |-> retval_2)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu = tu) ”
.

Definition mpz_gcd_partial_solve_wit_43_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (old: Z) (tv_v: Z) (tu_v: Z) (gz_v: Z) (tv: Z) (tu: Z) (odd: Z) (retval: Z) (retval_2: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 1)) (PreH2 : (same_sign tv_v size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (odd > tv_v)) (PreH7 : (retval_2 = 1)) (PreH8 : (0 <= retval)) (PreH9 : (odd > 0)) (PreH10 : ((odd % ( 2 ) ) = 1)) (PreH11 : (tu_v = (odd * (Z.pow (2) (retval)) ))) (PreH12 : (tu <> 0)) (PreH13 : (tv <> 0)) (PreH14 : (gz_v >= 0)) (PreH15 : (tu_v > 0)) (PreH16 : (tv_v > 0)) (PreH17 : ((tv_v % ( 2 ) ) = 1)) (PreH18 : (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v )) (PreH19 : ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (tv_v)) (Zabs (size)) )
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z tu odd )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu = tu) ” 
  &&  “ (size <> 1) ” 
  &&  “ (same_sign tv_v size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (odd > tv_v) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (tu_v = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (tu_v > 0) ” 
  &&  “ (tv_v > 0) ” 
  &&  “ ((tv_v % ( 2 ) ) = 1) ” 
  &&  “ (mpz_mul_2exp_fits (Zgcd (tu_v) (tv_v)) gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = ((Z.pow (2) (gz_v)) * (Zgcd (tu_v) (tv_v)) )) ”
  &&  (store_Z tu odd )
  **  (store_Z tv tv_v )
  **  (store_Z g_pre old )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_43 := mpz_gcd_partial_solve_wit_43_pure -> mpz_gcd_partial_solve_wit_43_aux.

Definition mpz_gcd_partial_solve_wit_44 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (tu_final: Z) (tv_final: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  (store_Z g_pre g_odd )
  **  (store_Z tu tu_final )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z tu tu_final )
  **  (store_Z g_pre g_odd )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_45 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (tv_final: Z) (gz_v: Z) (tu: Z) (tv: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z g_pre g_odd )
  **  (store_Z tv tv_final )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z tv tv_final )
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_46 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (gz_v: Z) (tu: Z) (tv: Z) (ptr: Z) (cap: Z) (size: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tu)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_47 := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (gz_v: Z) (tu: Z) (tv: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_48_pure := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (uz_v: Z) (vz_v: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "tu" ) )) # Ptr  |-> tu)
  **  ((( &( "tv" ) )) # Ptr  |-> tv)
  **  ((( &( "uz" ) )) # UInt64  |-> uz_v)
  **  ((( &( "vz" ) )) # UInt64  |-> vz_v)
  **  ((( &( "gz" ) )) # UInt64  |-> gz_v)
  **  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (g_pre = g_pre) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ”
.

Definition mpz_gcd_partial_solve_wit_48_aux := 
forall (v_pre: Z) (u_pre: Z) (g_pre: Z) (zv: Z) (zu: Z) (g_odd: Z) (gz_v: Z) (tu: Z) (tv: Z) (PreH1 : (tu <> 0)) (PreH2 : (tv <> 0)) (PreH3 : (gz_v >= 0)) (PreH4 : (mpz_mul_2exp_fits g_odd gz_v )) (PreH5 : ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) ))) ,
  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
|--
  “ (g_pre = g_pre) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ (tu <> 0) ” 
  &&  “ (tv <> 0) ” 
  &&  “ (gz_v >= 0) ” 
  &&  “ (mpz_mul_2exp_fits g_odd gz_v ) ” 
  &&  “ ((Zgcd (zu) (zv)) = (g_odd * (Z.pow (2) (gz_v)) )) ”
  &&  (store_Z g_pre g_odd )
  **  (store_Z u_pre zu )
  **  (store_Z v_pre zv )
.

Definition mpz_gcd_partial_solve_wit_48 := mpz_gcd_partial_solve_wit_48_pure -> mpz_gcd_partial_solve_wit_48_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include mpz_tdiv_r_read0_Strategy_Correct.

Axiom proof_of_mpz_gcd_safety_wit_1 : mpz_gcd_safety_wit_1.
Axiom proof_of_mpz_gcd_safety_wit_2 : mpz_gcd_safety_wit_2.
Axiom proof_of_mpz_gcd_safety_wit_3 : mpz_gcd_safety_wit_3.
Axiom proof_of_mpz_gcd_safety_wit_4 : mpz_gcd_safety_wit_4.
Axiom proof_of_mpz_gcd_safety_wit_5 : mpz_gcd_safety_wit_5.
Axiom proof_of_mpz_gcd_safety_wit_6 : mpz_gcd_safety_wit_6.
Axiom proof_of_mpz_gcd_safety_wit_7 : mpz_gcd_safety_wit_7.
Axiom proof_of_mpz_gcd_safety_wit_8 : mpz_gcd_safety_wit_8.
Axiom proof_of_mpz_gcd_safety_wit_9 : mpz_gcd_safety_wit_9.
Axiom proof_of_mpz_gcd_safety_wit_10 : mpz_gcd_safety_wit_10.
Axiom proof_of_mpz_gcd_safety_wit_11 : mpz_gcd_safety_wit_11.
Axiom proof_of_mpz_gcd_safety_wit_12 : mpz_gcd_safety_wit_12.
Axiom proof_of_mpz_gcd_safety_wit_13 : mpz_gcd_safety_wit_13.
Axiom proof_of_mpz_gcd_safety_wit_14 : mpz_gcd_safety_wit_14.
Axiom proof_of_mpz_gcd_safety_wit_15 : mpz_gcd_safety_wit_15.
Axiom proof_of_mpz_gcd_safety_wit_16 : mpz_gcd_safety_wit_16.
Axiom proof_of_mpz_gcd_safety_wit_17 : mpz_gcd_safety_wit_17.
Axiom proof_of_mpz_gcd_safety_wit_18 : mpz_gcd_safety_wit_18.
Axiom proof_of_mpz_gcd_safety_wit_19 : mpz_gcd_safety_wit_19.
Axiom proof_of_mpz_gcd_safety_wit_20 : mpz_gcd_safety_wit_20.
Axiom proof_of_mpz_gcd_safety_wit_21 : mpz_gcd_safety_wit_21.
Axiom proof_of_mpz_gcd_safety_wit_22 : mpz_gcd_safety_wit_22.
Axiom proof_of_mpz_gcd_safety_wit_23 : mpz_gcd_safety_wit_23.
Axiom proof_of_mpz_gcd_entail_wit_1 : mpz_gcd_entail_wit_1.
Axiom proof_of_mpz_gcd_entail_wit_2_1 : mpz_gcd_entail_wit_2_1.
Axiom proof_of_mpz_gcd_entail_wit_2_2 : mpz_gcd_entail_wit_2_2.
Axiom proof_of_mpz_gcd_entail_wit_2_3 : mpz_gcd_entail_wit_2_3.
Axiom proof_of_mpz_gcd_entail_wit_2_4 : mpz_gcd_entail_wit_2_4.
Axiom proof_of_mpz_gcd_entail_wit_3 : mpz_gcd_entail_wit_3.
Axiom proof_of_mpz_gcd_entail_wit_4_1 : mpz_gcd_entail_wit_4_1.
Axiom proof_of_mpz_gcd_entail_wit_4_2 : mpz_gcd_entail_wit_4_2.
Axiom proof_of_mpz_gcd_entail_wit_5 : mpz_gcd_entail_wit_5.
Axiom proof_of_mpz_gcd_entail_wit_6 : mpz_gcd_entail_wit_6.
Axiom proof_of_mpz_gcd_entail_wit_7 : mpz_gcd_entail_wit_7.
Axiom proof_of_mpz_gcd_entail_wit_8_1 : mpz_gcd_entail_wit_8_1.
Axiom proof_of_mpz_gcd_entail_wit_8_2 : mpz_gcd_entail_wit_8_2.
Axiom proof_of_mpz_gcd_entail_wit_9_1 : mpz_gcd_entail_wit_9_1.
Axiom proof_of_mpz_gcd_entail_wit_9_2 : mpz_gcd_entail_wit_9_2.
Axiom proof_of_mpz_gcd_entail_wit_9_3 : mpz_gcd_entail_wit_9_3.
Axiom proof_of_mpz_gcd_entail_wit_9_4 : mpz_gcd_entail_wit_9_4.
Axiom proof_of_mpz_gcd_entail_wit_9_5 : mpz_gcd_entail_wit_9_5.
Axiom proof_of_mpz_gcd_entail_wit_9_6 : mpz_gcd_entail_wit_9_6.
Axiom proof_of_mpz_gcd_entail_wit_9_7 : mpz_gcd_entail_wit_9_7.
Axiom proof_of_mpz_gcd_return_wit_1 : mpz_gcd_return_wit_1.
Axiom proof_of_mpz_gcd_return_wit_2 : mpz_gcd_return_wit_2.
Axiom proof_of_mpz_gcd_return_wit_3 : mpz_gcd_return_wit_3.
Axiom proof_of_mpz_gcd_partial_solve_wit_1 : mpz_gcd_partial_solve_wit_1.
Axiom proof_of_mpz_gcd_partial_solve_wit_2 : mpz_gcd_partial_solve_wit_2.
Axiom proof_of_mpz_gcd_partial_solve_wit_3 : mpz_gcd_partial_solve_wit_3.
Axiom proof_of_mpz_gcd_partial_solve_wit_4 : mpz_gcd_partial_solve_wit_4.
Axiom proof_of_mpz_gcd_partial_solve_wit_5 : mpz_gcd_partial_solve_wit_5.
Axiom proof_of_mpz_gcd_partial_solve_wit_6 : mpz_gcd_partial_solve_wit_6.
Axiom proof_of_mpz_gcd_partial_solve_wit_7 : mpz_gcd_partial_solve_wit_7.
Axiom proof_of_mpz_gcd_partial_solve_wit_8 : mpz_gcd_partial_solve_wit_8.
Axiom proof_of_mpz_gcd_partial_solve_wit_9 : mpz_gcd_partial_solve_wit_9.
Axiom proof_of_mpz_gcd_partial_solve_wit_10_pure : mpz_gcd_partial_solve_wit_10_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_10 : mpz_gcd_partial_solve_wit_10.
Axiom proof_of_mpz_gcd_partial_solve_wit_11 : mpz_gcd_partial_solve_wit_11.
Axiom proof_of_mpz_gcd_partial_solve_wit_12_pure : mpz_gcd_partial_solve_wit_12_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_12 : mpz_gcd_partial_solve_wit_12.
Axiom proof_of_mpz_gcd_partial_solve_wit_13 : mpz_gcd_partial_solve_wit_13.
Axiom proof_of_mpz_gcd_partial_solve_wit_14 : mpz_gcd_partial_solve_wit_14.
Axiom proof_of_mpz_gcd_partial_solve_wit_15 : mpz_gcd_partial_solve_wit_15.
Axiom proof_of_mpz_gcd_partial_solve_wit_16 : mpz_gcd_partial_solve_wit_16.
Axiom proof_of_mpz_gcd_partial_solve_wit_17 : mpz_gcd_partial_solve_wit_17.
Axiom proof_of_mpz_gcd_partial_solve_wit_18 : mpz_gcd_partial_solve_wit_18.
Axiom proof_of_mpz_gcd_partial_solve_wit_19_pure : mpz_gcd_partial_solve_wit_19_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_19 : mpz_gcd_partial_solve_wit_19.
Axiom proof_of_mpz_gcd_partial_solve_wit_20_pure : mpz_gcd_partial_solve_wit_20_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_20 : mpz_gcd_partial_solve_wit_20.
Axiom proof_of_mpz_gcd_partial_solve_wit_21_pure : mpz_gcd_partial_solve_wit_21_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_21 : mpz_gcd_partial_solve_wit_21.
Axiom proof_of_mpz_gcd_partial_solve_wit_22_pure : mpz_gcd_partial_solve_wit_22_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_22 : mpz_gcd_partial_solve_wit_22.
Axiom proof_of_mpz_gcd_partial_solve_wit_23 : mpz_gcd_partial_solve_wit_23.
Axiom proof_of_mpz_gcd_partial_solve_wit_24 : mpz_gcd_partial_solve_wit_24.
Axiom proof_of_mpz_gcd_partial_solve_wit_25 : mpz_gcd_partial_solve_wit_25.
Axiom proof_of_mpz_gcd_partial_solve_wit_26 : mpz_gcd_partial_solve_wit_26.
Axiom proof_of_mpz_gcd_partial_solve_wit_27 : mpz_gcd_partial_solve_wit_27.
Axiom proof_of_mpz_gcd_partial_solve_wit_28 : mpz_gcd_partial_solve_wit_28.
Axiom proof_of_mpz_gcd_partial_solve_wit_29 : mpz_gcd_partial_solve_wit_29.
Axiom proof_of_mpz_gcd_partial_solve_wit_30 : mpz_gcd_partial_solve_wit_30.
Axiom proof_of_mpz_gcd_partial_solve_wit_31_pure : mpz_gcd_partial_solve_wit_31_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_31 : mpz_gcd_partial_solve_wit_31.
Axiom proof_of_mpz_gcd_partial_solve_wit_32 : mpz_gcd_partial_solve_wit_32.
Axiom proof_of_mpz_gcd_partial_solve_wit_33 : mpz_gcd_partial_solve_wit_33.
Axiom proof_of_mpz_gcd_partial_solve_wit_34 : mpz_gcd_partial_solve_wit_34.
Axiom proof_of_mpz_gcd_partial_solve_wit_35 : mpz_gcd_partial_solve_wit_35.
Axiom proof_of_mpz_gcd_partial_solve_wit_36 : mpz_gcd_partial_solve_wit_36.
Axiom proof_of_mpz_gcd_partial_solve_wit_37_pure : mpz_gcd_partial_solve_wit_37_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_37 : mpz_gcd_partial_solve_wit_37.
Axiom proof_of_mpz_gcd_partial_solve_wit_38_pure : mpz_gcd_partial_solve_wit_38_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_38 : mpz_gcd_partial_solve_wit_38.
Axiom proof_of_mpz_gcd_partial_solve_wit_39 : mpz_gcd_partial_solve_wit_39.
Axiom proof_of_mpz_gcd_partial_solve_wit_40 : mpz_gcd_partial_solve_wit_40.
Axiom proof_of_mpz_gcd_partial_solve_wit_41_pure : mpz_gcd_partial_solve_wit_41_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_41 : mpz_gcd_partial_solve_wit_41.
Axiom proof_of_mpz_gcd_partial_solve_wit_42_pure : mpz_gcd_partial_solve_wit_42_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_42 : mpz_gcd_partial_solve_wit_42.
Axiom proof_of_mpz_gcd_partial_solve_wit_43_pure : mpz_gcd_partial_solve_wit_43_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_43 : mpz_gcd_partial_solve_wit_43.
Axiom proof_of_mpz_gcd_partial_solve_wit_44 : mpz_gcd_partial_solve_wit_44.
Axiom proof_of_mpz_gcd_partial_solve_wit_45 : mpz_gcd_partial_solve_wit_45.
Axiom proof_of_mpz_gcd_partial_solve_wit_46 : mpz_gcd_partial_solve_wit_46.
Axiom proof_of_mpz_gcd_partial_solve_wit_47 : mpz_gcd_partial_solve_wit_47.
Axiom proof_of_mpz_gcd_partial_solve_wit_48_pure : mpz_gcd_partial_solve_wit_48_pure.
Axiom proof_of_mpz_gcd_partial_solve_wit_48 : mpz_gcd_partial_solve_wit_48.

End VC_Correct.
