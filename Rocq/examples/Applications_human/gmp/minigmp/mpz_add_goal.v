From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_add -----*)

Definition mpz_add_safety_wit_1_nonalias :=
forall (l_nonalias: Z) (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m_nonalias size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n_nonalias size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_nonalias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_nonalias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_2_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
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

Definition mpz_add_safety_wit_3_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign n_nonalias size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : ((Z.lxor size size_2) >= 0)) (PreH4 : (same_sign m_nonalias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign n_nonalias size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_4_nonalias :=
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition mpz_add_safety_wit_4_nonalias_split_goal_1 :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_add_safety_wit_5_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= cap)) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zabs (rn_v)) <= cap)) (PreH5 : ((Zabs (bsize)) <= bcap)) (PreH6 : ((Z.lxor old_size bsize) >= 0)) (PreH7 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH8 : (same_sign za_r_eq_a old_size )) (PreH9 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_add_safety_wit_6_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_add_safety_wit_6_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_add_safety_wit_7_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign n_nonalias size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : ((Z.lxor size size_2) < 0)) (PreH4 : (same_sign m_nonalias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign n_nonalias size )) (PreH7 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_8_nonalias :=
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition mpz_add_safety_wit_8_nonalias_split_goal_1 :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_add_safety_wit_9_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= cap)) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zabs (rn_v)) <= cap)) (PreH5 : ((Zabs (bsize)) <= bcap)) (PreH6 : ((Z.lxor old_size bsize) < 0)) (PreH7 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH8 : (same_sign za_r_eq_a old_size )) (PreH9 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_add_safety_wit_10_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_add_safety_wit_10_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_add_entail_wit_1_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_3)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap_2)) (PreH6 : (r_pre = a_pre)),
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) retval )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (bptr: Z) (ptr: Z) (old_size: Z) (bcap: Z) (bsize: Z) (cap: Z),
  “ (r_pre = a_pre) ”
  &&  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zabs (retval)) <= cap) ”
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  “ ((Z.lxor old_size bsize) >= 0) ”
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (ptr_2: Z) (size_3: Z) (cap_4: Z) (PreH1 : (same_sign zb_r_eq_a size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_4)) (PreH3 : ((Z.lxor size size_2) >= 0)) (PreH4 : (same_sign zb_r_eq_a size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_3)) (PreH6 : (same_sign za_r_eq_a size )) (PreH7 : ((Zabs (size)) <= cap_2)) (PreH8 : (r_pre = a_pre)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_3)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) retval )
|--
  EX (ptr: Z) (old_size: Z) (cap: Z),
  “ (r_pre = a_pre) ”
  &&  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zabs (retval)) <= cap) ”
  &&  “ ((Zabs (size_3)) <= cap_4) ”
  &&  “ ((Z.lxor old_size size_3) >= 0) ”
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

Definition mpz_add_entail_wit_2_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_3)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap_2)) (PreH6 : (r_pre = a_pre)),
  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (bptr: Z) (ptr: Z) (old_size: Z) (bcap: Z) (bsize: Z) (cap: Z),
  “ (r_pre = a_pre) ”
  &&  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zabs (retval)) <= cap) ”
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  “ ((Z.lxor old_size bsize) < 0) ”
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap_2: Z) (size_2: Z) (cap_3: Z) (retval: Z) (ptr_2: Z) (size_3: Z) (cap_4: Z) (PreH1 : (same_sign zb_r_eq_a size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_4)) (PreH3 : ((Z.lxor size size_2) < 0)) (PreH4 : (same_sign zb_r_eq_a size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_3)) (PreH6 : (same_sign za_r_eq_a size )) (PreH7 : ((Zabs (size)) <= cap_2)) (PreH8 : (r_pre = a_pre)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (zb_r_eq_a)) (Zabs (size_3)) )
  **  (store_Z_with_old_size a_pre za_r_eq_a ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) retval )
|--
  EX (ptr: Z) (old_size: Z) (cap: Z),
  “ (r_pre = a_pre) ”
  &&  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zabs (retval)) <= cap) ”
  &&  “ ((Zabs (size_3)) <= cap_4) ”
  &&  “ ((Z.lxor old_size size_3) < 0) ”
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

Definition mpz_add_return_wit_1_nonalias :=
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
|--
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre (n_nonalias + m_nonalias ) )
) \/
(
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ (same_sign (n_nonalias + m_nonalias ) retval ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
).

Definition mpz_add_return_wit_1_nonalias_split_goal_1 :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ (same_sign (n_nonalias + m_nonalias ) retval ) ”
.

Definition mpz_add_return_wit_1_nonalias_split_goal_spatial :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_return_wit_2_nonalias :=
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
|--
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre (n_nonalias + m_nonalias ) )
) \/
(
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
  &&  “ (same_sign (n_nonalias + m_nonalias ) (-retval) ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
).

Definition mpz_add_return_wit_2_nonalias_split_goal_1 :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
.

Definition mpz_add_return_wit_2_nonalias_split_goal_2 :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ (same_sign (n_nonalias + m_nonalias ) (-retval) ) ”
.

Definition mpz_add_return_wit_2_nonalias_split_goal_spatial :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_return_wit_3_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  (store_Z a_pre (za_r_eq_a + zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (rn_v <= INT_MAX)) (PreH2 : (rn_v >= INT_MIN)) (PreH3 : (old_size >= 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) >= 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn_v)
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z),
  “ (same_sign zb_r_eq_a bsize ) ”
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  “ (same_sign (za_r_eq_a + zb_r_eq_a ) size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a + zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_add_return_wit_4_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  (store_Z a_pre (za_r_eq_a + zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : ((-rn_v) <= INT_MAX)) (PreH2 : ((-rn_v) >= INT_MIN)) (PreH3 : (old_size < 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) >= 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn_v))
  **  (mpd_store_Z_compact UINT_MOD ptr ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z),
  “ (same_sign zb_r_eq_a bsize ) ”
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  “ (same_sign (za_r_eq_a + zb_r_eq_a ) size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a + zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_add_return_wit_5_nonalias :=
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
|--
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre (n_nonalias + m_nonalias ) )
) \/
(
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ (same_sign (n_nonalias + m_nonalias ) retval ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
).

Definition mpz_add_return_wit_5_nonalias_split_goal_1 :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ (same_sign (n_nonalias + m_nonalias ) retval ) ”
.

Definition mpz_add_return_wit_5_nonalias_split_goal_spatial :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_return_wit_6_nonalias :=
(
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
|--
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre (n_nonalias + m_nonalias ) )
) \/
(
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
  &&  “ (same_sign (n_nonalias + m_nonalias ) (-retval) ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
).

Definition mpz_add_return_wit_6_nonalias_split_goal_1 :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
.

Definition mpz_add_return_wit_6_nonalias_split_goal_2 :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  “ (same_sign (n_nonalias + m_nonalias ) (-retval) ) ”
.

Definition mpz_add_return_wit_6_nonalias_split_goal_spatial :=
forall (m_nonalias: Z) (n_nonalias: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n_nonalias size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m_nonalias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n_nonalias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
|--
  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n_nonalias + m_nonalias ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_return_wit_7_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  (store_Z a_pre (za_r_eq_a + zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (rn_v <= INT_MAX)) (PreH2 : (rn_v >= INT_MIN)) (PreH3 : (old_size >= 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) < 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn_v)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z),
  “ (same_sign zb_r_eq_a bsize ) ”
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  “ (same_sign (za_r_eq_a + zb_r_eq_a ) size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a + zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_add_return_wit_8_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  (store_Z a_pre (za_r_eq_a + zb_r_eq_a ) )
  **  (store_Z b_pre zb_r_eq_a )
) \/
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : ((-rn_v) <= INT_MAX)) (PreH2 : ((-rn_v) >= INT_MIN)) (PreH3 : (old_size < 0)) (PreH4 : (r_pre = a_pre)) (PreH5 : (0 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (rn_v)) <= cap)) (PreH8 : ((Zabs (bsize)) <= bcap)) (PreH9 : ((Z.lxor old_size bsize) < 0)) (PreH10 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH11 : (same_sign za_r_eq_a old_size )) (PreH12 : (same_sign zb_r_eq_a bsize )),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn_v))
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (Zabs (rn_v)) )
  **  (UIntArray.undef_seg ptr (Zabs (rn_v)) cap )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
|--
  EX (size: Z),
  “ (same_sign zb_r_eq_a bsize ) ”
  &&  “ ((Zabs (bsize)) <= bcap) ”
  &&  “ (same_sign (za_r_eq_a + zb_r_eq_a ) size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) (Zabs (bsize)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((za_r_eq_a + zb_r_eq_a ))) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
).

Definition mpz_add_partial_solve_wit_1_nonalias :=
forall (l_nonalias: Z) (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z),
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre l_nonalias )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre l_nonalias )
.

Definition mpz_add_partial_solve_wit_2_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = a_pre)),
  (store_Z a_pre za_r_eq_a )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
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

Definition mpz_add_partial_solve_wit_3_nonalias :=
forall (l_nonalias: Z) (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n_nonalias size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre l_nonalias )
|--
  EX (ptr_2: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_nonalias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_nonalias )
.

Definition mpz_add_partial_solve_wit_4_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign za_r_eq_a size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (r_pre = a_pre)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (za_r_eq_a)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (ptr_2: Z) (size_2: Z) (cap_2: Z),
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

Definition mpz_add_partial_solve_wit_5_nonalias :=
forall (l_nonalias: Z) (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign m_nonalias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n_nonalias size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_nonalias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_nonalias )
|--
  “ ((Z.lxor size size_2) >= 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre l_nonalias )
.

Definition mpz_add_partial_solve_wit_6_r_eq_a_pure :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)),
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

Definition mpz_add_partial_solve_wit_6_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)),
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

Definition mpz_add_partial_solve_wit_6_r_eq_a := mpz_add_partial_solve_wit_6_r_eq_a_pure -> mpz_add_partial_solve_wit_6_r_eq_a_aux.

Definition mpz_add_partial_solve_wit_7_nonalias :=
forall (l_nonalias: Z) (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign m_nonalias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n_nonalias size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_nonalias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_nonalias )
|--
  “ ((Z.lxor size size_2) < 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z r_pre l_nonalias )
.

Definition mpz_add_partial_solve_wit_8_r_eq_a_pure :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)),
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

Definition mpz_add_partial_solve_wit_8_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign zb_r_eq_a size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign za_r_eq_a size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (r_pre = a_pre)),
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

Definition mpz_add_partial_solve_wit_8_r_eq_a := mpz_add_partial_solve_wit_8_r_eq_a_pure -> mpz_add_partial_solve_wit_8_r_eq_a_aux.

Definition mpz_add_partial_solve_wit_9_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign m_nonalias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n_nonalias size )) (PreH5 : ((Zabs (size)) <= cap)),
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
|--
  EX (ptr: Z) (size_3: Z) (cap_3: Z),
  “ (same_sign n_nonalias size_3 ) ”
  &&  “ ((Zabs (size_3)) <= cap_3) ”
  &&  “ ((Z.lxor size size_2) >= 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
.

Definition mpz_add_partial_solve_wit_10_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 >= 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
|--
  EX (ptr_2: Z) (cap_4: Z),
  “ (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval ) ”
  &&  “ ((Zabs (retval)) <= cap_4) ”
  &&  “ (size_3 >= 0) ”
  &&  “ (same_sign n_nonalias size_3 ) ”
  &&  “ ((Zabs (size_3)) <= cap_3) ”
  &&  “ ((Z.lxor size size_2) >= 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_partial_solve_wit_11_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval )
|--
  EX (ptr_2: Z) (cap_4: Z),
  “ (same_sign ((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ) retval ) ”
  &&  “ ((Zabs (retval)) <= cap_4) ”
  &&  “ (size_3 < 0) ”
  &&  “ (same_sign n_nonalias size_3 ) ”
  &&  “ ((Zabs (size_3)) <= cap_3) ”
  &&  “ ((Z.lxor size size_2) >= 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) + (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_partial_solve_wit_12_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  &&  “ ((Z.lxor old_size bsize) >= 0) ”
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

Definition mpz_add_partial_solve_wit_13_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) >= 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) + (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  &&  “ ((Z.lxor old_size bsize) >= 0) ”
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

Definition mpz_add_partial_solve_wit_14_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign m_nonalias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n_nonalias size )) (PreH5 : ((Zabs (size)) <= cap)),
  (store_Z a_pre n_nonalias )
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
|--
  EX (ptr: Z) (size_3: Z) (cap_3: Z),
  “ (same_sign n_nonalias size_3 ) ”
  &&  “ ((Zabs (size_3)) <= cap_3) ”
  &&  “ ((Z.lxor size size_2) < 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
.

Definition mpz_add_partial_solve_wit_15_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 >= 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
|--
  EX (ptr_2: Z) (cap_4: Z),
  “ (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval ) ”
  &&  “ ((Zabs (retval)) <= cap_4) ”
  &&  “ (size_3 >= 0) ”
  &&  “ (same_sign n_nonalias size_3 ) ”
  &&  “ ((Zabs (size_3)) <= cap_3) ”
  &&  “ ((Z.lxor size size_2) < 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_partial_solve_wit_16_nonalias :=
forall (m_nonalias: Z) (n_nonalias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n_nonalias size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m_nonalias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n_nonalias size )) (PreH8 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
  **  (store_Z_remain_size r_pre ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval )
|--
  EX (ptr_2: Z) (cap_4: Z),
  “ (same_sign ((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ) retval ) ”
  &&  “ ((Zabs (retval)) <= cap_4) ”
  &&  “ (size_3 < 0) ”
  &&  “ (same_sign n_nonalias size_3 ) ”
  &&  “ ((Zabs (size_3)) <= cap_3) ”
  &&  “ ((Z.lxor size size_2) < 0) ”
  &&  “ (same_sign m_nonalias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_nonalias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n_nonalias)) - (Zabs (m_nonalias)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_nonalias)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m_nonalias )
.

Definition mpz_add_partial_solve_wit_17_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size >= 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  &&  “ ((Z.lxor old_size bsize) < 0) ”
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

Definition mpz_add_partial_solve_wit_18_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (old_size: Z) (cap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rn_v: Z) (PreH1 : (old_size < 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (0 <= cap)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (rn_v)) <= cap)) (PreH6 : ((Zabs (bsize)) <= bcap)) (PreH7 : ((Z.lxor old_size bsize) < 0)) (PreH8 : (same_sign ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ) rn_v )) (PreH9 : (same_sign za_r_eq_a old_size )) (PreH10 : (same_sign zb_r_eq_a bsize )),
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
  &&  “ ((Z.lxor old_size bsize) < 0) ”
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

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_add_safety_wit_1_nonalias : mpz_add_safety_wit_1_nonalias.
Axiom proof_of_mpz_add_safety_wit_2_r_eq_a : mpz_add_safety_wit_2_r_eq_a.
Axiom proof_of_mpz_add_safety_wit_3_nonalias : mpz_add_safety_wit_3_nonalias.
Axiom proof_of_mpz_add_safety_wit_4_nonalias : mpz_add_safety_wit_4_nonalias.
Axiom proof_of_mpz_add_safety_wit_5_r_eq_a : mpz_add_safety_wit_5_r_eq_a.
Axiom proof_of_mpz_add_safety_wit_6_r_eq_a : mpz_add_safety_wit_6_r_eq_a.
Axiom proof_of_mpz_add_safety_wit_7_nonalias : mpz_add_safety_wit_7_nonalias.
Axiom proof_of_mpz_add_safety_wit_8_nonalias : mpz_add_safety_wit_8_nonalias.
Axiom proof_of_mpz_add_safety_wit_9_r_eq_a : mpz_add_safety_wit_9_r_eq_a.
Axiom proof_of_mpz_add_safety_wit_10_r_eq_a : mpz_add_safety_wit_10_r_eq_a.
Axiom proof_of_mpz_add_entail_wit_1_r_eq_a : mpz_add_entail_wit_1_r_eq_a.
Axiom proof_of_mpz_add_entail_wit_2_r_eq_a : mpz_add_entail_wit_2_r_eq_a.
Axiom proof_of_mpz_add_return_wit_1_nonalias : mpz_add_return_wit_1_nonalias.
Axiom proof_of_mpz_add_return_wit_2_nonalias : mpz_add_return_wit_2_nonalias.
Axiom proof_of_mpz_add_return_wit_3_r_eq_a : mpz_add_return_wit_3_r_eq_a.
Axiom proof_of_mpz_add_return_wit_4_r_eq_a : mpz_add_return_wit_4_r_eq_a.
Axiom proof_of_mpz_add_return_wit_5_nonalias : mpz_add_return_wit_5_nonalias.
Axiom proof_of_mpz_add_return_wit_6_nonalias : mpz_add_return_wit_6_nonalias.
Axiom proof_of_mpz_add_return_wit_7_r_eq_a : mpz_add_return_wit_7_r_eq_a.
Axiom proof_of_mpz_add_return_wit_8_r_eq_a : mpz_add_return_wit_8_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_1_nonalias : mpz_add_partial_solve_wit_1_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_2_r_eq_a : mpz_add_partial_solve_wit_2_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_3_nonalias : mpz_add_partial_solve_wit_3_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_4_r_eq_a : mpz_add_partial_solve_wit_4_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_5_nonalias : mpz_add_partial_solve_wit_5_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_6_r_eq_a_pure : mpz_add_partial_solve_wit_6_r_eq_a_pure.
Axiom proof_of_mpz_add_partial_solve_wit_6_r_eq_a : mpz_add_partial_solve_wit_6_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_7_nonalias : mpz_add_partial_solve_wit_7_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_8_r_eq_a_pure : mpz_add_partial_solve_wit_8_r_eq_a_pure.
Axiom proof_of_mpz_add_partial_solve_wit_8_r_eq_a : mpz_add_partial_solve_wit_8_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_9_nonalias : mpz_add_partial_solve_wit_9_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_10_nonalias : mpz_add_partial_solve_wit_10_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_11_nonalias : mpz_add_partial_solve_wit_11_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_12_r_eq_a : mpz_add_partial_solve_wit_12_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_13_r_eq_a : mpz_add_partial_solve_wit_13_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_14_nonalias : mpz_add_partial_solve_wit_14_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_15_nonalias : mpz_add_partial_solve_wit_15_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_16_nonalias : mpz_add_partial_solve_wit_16_nonalias.
Axiom proof_of_mpz_add_partial_solve_wit_17_r_eq_a : mpz_add_partial_solve_wit_17_r_eq_a.
Axiom proof_of_mpz_add_partial_solve_wit_18_r_eq_a : mpz_add_partial_solve_wit_18_r_eq_a.

End VC_Correct.
