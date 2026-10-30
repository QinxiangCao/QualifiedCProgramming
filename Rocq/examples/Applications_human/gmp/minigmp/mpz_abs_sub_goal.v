From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_abs_sub -----*)

Definition mpz_abs_sub_safety_wit_1_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH2 : (retval_3 = (-1))) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (same_sign m_non_alias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (same_sign n_non_alias size )) (PreH8 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_2_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (same_sign m_non_alias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (same_sign n_non_alias size )) (PreH8 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_3_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (same_sign m_non_alias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (same_sign n_non_alias size )) (PreH8 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_4_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH2 : (retval_3 = (-1))) (PreH3 : (retval_2 = (Zabs (bsize)))) (PreH4 : (retval = (Zabs (rsize)))) (PreH5 : (r_pre = a_pre)) (PreH6 : (INT_MIN < rsize)) (PreH7 : (rsize <= INT_MAX)) (PreH8 : (INT_MIN < bsize)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (0 <= rcap)) (PreH11 : (rcap <= INT_MAX)) (PreH12 : (0 <= bcap)) (PreH13 : (bcap <= INT_MAX)) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (same_sign za_r_eq_a rsize )) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_5_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_2 = (Zabs (bsize)))) (PreH4 : (retval = (Zabs (rsize)))) (PreH5 : (r_pre = a_pre)) (PreH6 : (INT_MIN < rsize)) (PreH7 : (rsize <= INT_MAX)) (PreH8 : (INT_MIN < bsize)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (0 <= rcap)) (PreH11 : (rcap <= INT_MAX)) (PreH12 : (0 <= bcap)) (PreH13 : (bcap <= INT_MAX)) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (same_sign za_r_eq_a rsize )) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_6_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = (Zabs (bsize)))) (PreH4 : (retval = (Zabs (rsize)))) (PreH5 : (r_pre = a_pre)) (PreH6 : (INT_MIN < rsize)) (PreH7 : (rsize <= INT_MAX)) (PreH8 : (INT_MIN < bsize)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (0 <= rcap)) (PreH11 : (rcap <= INT_MAX)) (PreH12 : (0 <= bcap)) (PreH13 : (bcap <= INT_MAX)) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (same_sign za_r_eq_a rsize )) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_7_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m_non_alias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n_non_alias size )) (PreH9 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_8_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m_non_alias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n_non_alias size )) (PreH9 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_9_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m_non_alias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n_non_alias size )) (PreH9 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_10_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_11_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_12_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_13_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m_non_alias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n_non_alias size )) (PreH9 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_14_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m_non_alias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n_non_alias size )) (PreH9 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_15_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_16_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_17_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_18_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_19_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_20_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_safety_wit_21_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH6 : (cmp < 0)) (PreH7 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH8 : (cmp = (-1))) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (bn <= rcap_new)) (PreH18 : (a = r_pre)) (PreH19 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_safety_wit_22_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH6 : (cmp < 0)) (PreH7 : (cmp <= 0)) (PreH8 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH9 : (cmp = (-1))) (PreH10 : (bn = (Zabs (b__mp_size)))) (PreH11 : (same_sign m_non_alias b__mp_size )) (PreH12 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH13 : (an = (Zabs (a__mp_size)))) (PreH14 : (same_sign n_non_alias a__mp_size )) (PreH15 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH16 : (same_sign l_non_alias rsize )) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (rcap >= 0)) (PreH19 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH20 : (r__mp_d = rp)) (PreH21 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH22 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_abs_sub_safety_wit_23_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_24_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_entail_wit_1_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = a_pre)),
  (store_Z a_pre za_r_eq_a )
  **  (store_Z b_pre zb_r_eq_a )
|--
  EX (bptr: Z) (rptr: Z) (bcap: Z) (rcap: Z) (bsize: Z) (rsize: Z),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (cap_2 <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_2 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (0 <= cap_2)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_3 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (cap <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_4 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (0 <= cap)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_5 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (size_2 <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_6 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (INT_MIN < size_2)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_7 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (size <= INT_MAX)
.

Definition mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_8 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign zb_r_eq_a size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign za_r_eq_a size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (r_pre = a_pre)),
  (INT_MIN < size)
.

Definition mpz_abs_sub_entail_wit_2_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (bsize)))) (PreH5 : (retval = (Zabs (rsize)))) (PreH6 : (r_pre = a_pre)) (PreH7 : (INT_MIN < rsize)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (INT_MIN < bsize)) (PreH10 : (bsize <= INT_MAX)) (PreH11 : (0 <= rcap)) (PreH12 : (rcap <= INT_MAX)) (PreH13 : (0 <= bcap)) (PreH14 : (bcap <= INT_MAX)) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (same_sign za_r_eq_a rsize )) (PreH17 : ((Zabs (bsize)) <= bcap)) (PreH18 : (same_sign zb_r_eq_a bsize )),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (bsize)))) (PreH7 : (retval = (Zabs (rsize)))) (PreH8 : (r_pre = a_pre)) (PreH9 : (INT_MIN < rsize)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (INT_MIN < bsize)) (PreH12 : (bsize <= INT_MAX)) (PreH13 : (0 <= rcap)) (PreH14 : (rcap <= INT_MAX)) (PreH15 : (0 <= bcap)) (PreH16 : (bcap <= INT_MAX)) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_entail_wit_2_r_eq_a_split_goal_spatial :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (bsize)))) (PreH7 : (retval = (Zabs (rsize)))) (PreH8 : (r_pre = a_pre)) (PreH9 : (INT_MIN < rsize)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (INT_MIN < bsize)) (PreH12 : (bsize <= INT_MAX)) (PreH13 : (0 <= rcap)) (PreH14 : (rcap <= INT_MAX)) (PreH15 : (0 <= bcap)) (PreH16 : (bcap <= INT_MAX)) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (same_sign za_r_eq_a rsize )) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_entail_wit_3_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = 1)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)),
  TT && emp 
|--
  “ (1 <= an) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_3_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)),
  (1 <= an)
.

Definition mpz_abs_sub_entail_wit_4_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (1 <= an)) (PreH2 : (an <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (bn <= INT_MAX)) (PreH7 : (cmp <= INT_MAX)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (bn >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (an >= INT_MIN)) (PreH2 : (1 <= an)) (PreH3 : (an <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (bn >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp > 0)) (PreH16 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = 1)) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)),
  TT && emp 
|--
  “ (0 <= bn) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_4_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (an >= INT_MIN)) (PreH2 : (1 <= an)) (PreH3 : (an <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (bn >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp > 0)) (PreH16 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = 1)) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)),
  (0 <= bn)
.

Definition mpz_abs_sub_entail_wit_5_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= bn)) (PreH2 : (bn <= INT_MAX)) (PreH3 : (an >= INT_MIN)) (PreH4 : (1 <= an)) (PreH5 : (an <= INT_MAX)) (PreH6 : (bcap <= INT_MAX)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (bn <= INT_MAX)) (PreH10 : (cmp <= INT_MAX)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (rcap >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (cmp >= INT_MIN)) (PreH17 : (cmp > 0)) (PreH18 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = 1)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap)) (PreH25 : (0 <= rcap)) (PreH26 : (rcap <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_entail_wit_6_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m_non_alias size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n_non_alias size )) (PreH9 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
|--
  EX (rptr: Z) (b__mp_d: Z) (a__mp_d: Z) (rcap: Z) (rsize: Z) (a__mp_alloc: Z) (a__mp_size: Z) (b__mp_alloc: Z) (b__mp_size: Z),
  “ (retval_3 > 0) ”
  &&  “ ((Zabs (n_non_alias)) > (Zabs (m_non_alias))) ”
  &&  “ (retval_3 = 1) ”
  &&  “ (retval_2 = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (retval = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) retval )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) retval_2 )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l_non_alias size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (size_2)))) (PreH7 : (same_sign m_non_alias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (retval = (Zabs (size)))) (PreH10 : (same_sign n_non_alias size )) (PreH11 : ((Zabs (size)) <= cap)),
  TT && emp 
|--
  “ (cap_3 >= 0) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_6_non_alias_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l_non_alias size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (size_2)))) (PreH7 : (same_sign m_non_alias size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (retval = (Zabs (size)))) (PreH10 : (same_sign n_non_alias size )) (PreH11 : ((Zabs (size)) <= cap)),
  (cap_3 >= 0)
.

Definition mpz_abs_sub_entail_wit_7_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b__mp_size_2: Z) (b__mp_alloc_2: Z) (an: Z) (a__mp_size_2: Z) (a__mp_alloc_2: Z) (a__mp_d_2: Z) (b__mp_d_2: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l_non_alias rsize_2 )) (PreH2 : (z__mp_alloc = (Z.max (an) (rcap_2)))) (PreH3 : (cmp > 0)) (PreH4 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH5 : (cmp = 1)) (PreH6 : (bn = (Zabs (b__mp_size_2)))) (PreH7 : (same_sign m_non_alias b__mp_size_2 )) (PreH8 : ((Zabs (b__mp_size_2)) <= b__mp_alloc_2)) (PreH9 : (an = (Zabs (a__mp_size_2)))) (PreH10 : (same_sign n_non_alias a__mp_size_2 )) (PreH11 : ((Zabs (a__mp_size_2)) <= a__mp_alloc_2)) (PreH12 : ((Zabs (rsize_2)) <= rcap_2)) (PreH13 : (same_sign l_non_alias rsize_2 )) (PreH14 : (rcap_2 >= 0)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l_non_alias)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max (an) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d_2 (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d_2 (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d_2 (Zabs (b__mp_size_2)) b__mp_alloc_2 )
  **  (UIntArray.undef_seg a__mp_d_2 (Zabs (a__mp_size_2)) a__mp_alloc_2 )
|--
  EX (b__mp_d: Z) (a__mp_d: Z) (r__mp_d: Z) (r__mp_alloc: Z) (rcap: Z) (rsize: Z) (a__mp_alloc: Z) (a__mp_size: Z) (b__mp_alloc: Z) (b__mp_size: Z),
  “ (cmp > 0) ”
  &&  “ ((Zabs (n_non_alias)) > (Zabs (m_non_alias))) ”
  &&  “ (cmp = 1) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ”
  &&  “ (r__mp_d = retval) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) ) ”
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max (an) (1))) (rcap)) )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b__mp_size_2: Z) (b__mp_alloc_2: Z) (an: Z) (a__mp_size_2: Z) (a__mp_alloc_2: Z) (a__mp_d_2: Z) (b__mp_d_2: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l_non_alias rsize_2 )) (PreH2 : (z__mp_alloc = (Z.max (an) (rcap_2)))) (PreH3 : (cmp > 0)) (PreH4 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH5 : (cmp = 1)) (PreH6 : (bn = (Zabs (b__mp_size_2)))) (PreH7 : (same_sign m_non_alias b__mp_size_2 )) (PreH8 : ((Zabs (b__mp_size_2)) <= b__mp_alloc_2)) (PreH9 : (an = (Zabs (a__mp_size_2)))) (PreH10 : (same_sign n_non_alias a__mp_size_2 )) (PreH11 : ((Zabs (a__mp_size_2)) <= a__mp_alloc_2)) (PreH12 : ((Zabs (rsize_2)) <= rcap_2)) (PreH13 : (same_sign l_non_alias rsize_2 )) (PreH14 : (rcap_2 >= 0)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l_non_alias)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max (an) (rcap_2)) )
  **  (mpd_store_Z_compact UINT_MOD a__mp_d_2 (Zabs (n_non_alias)) an )
  **  (mpd_store_Z_compact UINT_MOD b__mp_d_2 (Zabs (m_non_alias)) bn )
|--
  EX (rcap: Z),
  “ (z__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ”
  &&  “ (z__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ”
  &&  “ (cmp > 0) ”
  &&  “ ((Zabs (n_non_alias)) > (Zabs (m_non_alias))) ”
  &&  “ (cmp = 1) ”
  &&  “ (bn = (Zabs (b__mp_size_2))) ”
  &&  “ (same_sign m_non_alias b__mp_size_2 ) ”
  &&  “ ((Zabs (b__mp_size_2)) <= b__mp_alloc_2) ”
  &&  “ (an = (Zabs (a__mp_size_2))) ”
  &&  “ (same_sign n_non_alias a__mp_size_2 ) ”
  &&  “ ((Zabs (a__mp_size_2)) <= a__mp_alloc_2) ”
  &&  “ (same_sign l_non_alias rsize_2 ) ”
  &&  “ ((Zabs (rsize_2)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize_2)) ) ”
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD a__mp_d_2 (Zabs (n_non_alias)) an )
  **  (mpd_store_Z_compact UINT_MOD b__mp_d_2 (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max (an) (1))) (rcap)) )
).

Definition mpz_abs_sub_entail_wit_8_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z__mp_alloc = (Z.max (an) (rcap)))) (PreH3 : (0 <= rcap)) (PreH4 : (rcap <= INT_MAX)) (PreH5 : (0 <= bn)) (PreH6 : (bn <= INT_MAX)) (PreH7 : (an >= INT_MIN)) (PreH8 : (1 <= an)) (PreH9 : (an <= INT_MAX)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (rsize <= INT_MAX)) (PreH13 : (bn <= INT_MAX)) (PreH14 : (cmp <= INT_MAX)) (PreH15 : (bcap >= INT_MIN)) (PreH16 : (bsize >= INT_MIN)) (PreH17 : (rcap >= INT_MIN)) (PreH18 : (rsize >= INT_MIN)) (PreH19 : (bn >= INT_MIN)) (PreH20 : (cmp >= INT_MIN)) (PreH21 : (cmp > 0)) (PreH22 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH23 : (cmp = 1)) (PreH24 : (an = (Zabs (rsize)))) (PreH25 : (bn = (Zabs (bsize)))) (PreH26 : (same_sign za_r_eq_a rsize )) (PreH27 : (same_sign zb_r_eq_a bsize )) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (0 <= rcap)) (PreH30 : (rcap <= INT_MAX)) (PreH31 : ((Zabs (bsize)) <= bcap)) (PreH32 : (r_pre = a_pre)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max (an) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  EX (rcap_new: Z),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (z__mp_alloc <= INT_MAX)) (PreH2 : (z__mp_alloc >= INT_MIN)) (PreH3 : (same_sign za_r_eq_a rsize )) (PreH4 : (z__mp_alloc = (Z.max (an) (rcap)))) (PreH5 : (0 <= rcap)) (PreH6 : (rcap <= INT_MAX)) (PreH7 : (0 <= bn)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (an >= INT_MIN)) (PreH10 : (1 <= an)) (PreH11 : (an <= INT_MAX)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (bn <= INT_MAX)) (PreH16 : (cmp <= INT_MAX)) (PreH17 : (bcap >= INT_MIN)) (PreH18 : (bsize >= INT_MIN)) (PreH19 : (rcap >= INT_MIN)) (PreH20 : (rsize >= INT_MIN)) (PreH21 : (bn >= INT_MIN)) (PreH22 : (cmp >= INT_MIN)) (PreH23 : (cmp > 0)) (PreH24 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH25 : (cmp = 1)) (PreH26 : (an = (Zabs (rsize)))) (PreH27 : (bn = (Zabs (bsize)))) (PreH28 : (same_sign za_r_eq_a rsize )) (PreH29 : (same_sign zb_r_eq_a bsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (0 <= rcap)) (PreH32 : (rcap <= INT_MAX)) (PreH33 : ((Zabs (bsize)) <= bcap)) (PreH34 : (r_pre = a_pre)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max (an) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  EX (rcap_new: Z),
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

Definition mpz_abs_sub_entail_wit_9_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_entail_wit_9_r_eq_a_split_goal_spatial :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_entail_wit_10_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (cmp < 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = (-1))) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap)) (PreH9 : (0 <= rcap)) (PreH10 : (rcap <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)),
  TT && emp 
|--
  “ (1 <= bn) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_10_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)),
  (1 <= bn)
.

Definition mpz_abs_sub_entail_wit_11_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (1 <= bn)) (PreH2 : (bn <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (an <= INT_MAX)) (PreH7 : (cmp <= INT_MAX)) (PreH8 : (bcap >= INT_MIN)) (PreH9 : (bsize >= INT_MIN)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (0 <= rcap)) (PreH23 : (rcap <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bn >= INT_MIN)) (PreH2 : (1 <= bn)) (PreH3 : (bn <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (an <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (an >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp < 0)) (PreH16 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = (-1))) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)),
  TT && emp 
|--
  “ (0 <= an) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_11_r_eq_a_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (bn >= INT_MIN)) (PreH2 : (1 <= bn)) (PreH3 : (bn <= INT_MAX)) (PreH4 : (bcap <= INT_MAX)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (an <= INT_MAX)) (PreH8 : (cmp <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (rcap >= INT_MIN)) (PreH12 : (rsize >= INT_MIN)) (PreH13 : (an >= INT_MIN)) (PreH14 : (cmp >= INT_MIN)) (PreH15 : (cmp < 0)) (PreH16 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH17 : (cmp = (-1))) (PreH18 : (an = (Zabs (rsize)))) (PreH19 : (bn = (Zabs (bsize)))) (PreH20 : (same_sign za_r_eq_a rsize )) (PreH21 : (same_sign zb_r_eq_a bsize )) (PreH22 : ((Zabs (rsize)) <= rcap)) (PreH23 : (0 <= rcap)) (PreH24 : (rcap <= INT_MAX)) (PreH25 : ((Zabs (bsize)) <= bcap)) (PreH26 : (r_pre = a_pre)),
  (0 <= an)
.

Definition mpz_abs_sub_entail_wit_12_r_eq_a :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= an)) (PreH2 : (an <= INT_MAX)) (PreH3 : (bn >= INT_MIN)) (PreH4 : (1 <= bn)) (PreH5 : (bn <= INT_MAX)) (PreH6 : (bcap <= INT_MAX)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (an <= INT_MAX)) (PreH10 : (cmp <= INT_MAX)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (rcap >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (an >= INT_MIN)) (PreH16 : (cmp >= INT_MIN)) (PreH17 : (cmp < 0)) (PreH18 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = (-1))) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap)) (PreH25 : (0 <= rcap)) (PreH26 : (rcap <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_entail_wit_13_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
|--
  EX (rptr: Z) (b__mp_d: Z) (a__mp_d: Z) (rcap: Z) (rsize: Z) (a__mp_alloc: Z) (a__mp_size: Z) (b__mp_alloc: Z) (b__mp_size: Z),
  “ (retval_3 < 0) ”
  &&  “ (retval_3 <= 0) ”
  &&  “ ((Zabs (n_non_alias)) < (Zabs (m_non_alias))) ”
  &&  “ (retval_3 = (-1)) ”
  &&  “ (retval_2 = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (retval = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) retval )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) retval_2 )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l_non_alias size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (size_2)))) (PreH8 : (same_sign m_non_alias size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (same_sign n_non_alias size )) (PreH12 : ((Zabs (size)) <= cap)),
  TT && emp 
|--
  “ (cap_3 >= 0) ”
  &&  emp
).

Definition mpz_abs_sub_entail_wit_13_non_alias_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l_non_alias size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (size_2)))) (PreH8 : (same_sign m_non_alias size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (same_sign n_non_alias size )) (PreH12 : ((Zabs (size)) <= cap)),
  (cap_3 >= 0)
.

Definition mpz_abs_sub_entail_wit_14_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b__mp_size_2: Z) (b__mp_alloc_2: Z) (an: Z) (a__mp_size_2: Z) (a__mp_alloc_2: Z) (a__mp_d_2: Z) (b__mp_d_2: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l_non_alias rsize_2 )) (PreH2 : (z__mp_alloc = (Z.max (bn) (rcap_2)))) (PreH3 : (cmp < 0)) (PreH4 : (cmp <= 0)) (PreH5 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH6 : (cmp = (-1))) (PreH7 : (bn = (Zabs (b__mp_size_2)))) (PreH8 : (same_sign m_non_alias b__mp_size_2 )) (PreH9 : ((Zabs (b__mp_size_2)) <= b__mp_alloc_2)) (PreH10 : (an = (Zabs (a__mp_size_2)))) (PreH11 : (same_sign n_non_alias a__mp_size_2 )) (PreH12 : ((Zabs (a__mp_size_2)) <= a__mp_alloc_2)) (PreH13 : ((Zabs (rsize_2)) <= rcap_2)) (PreH14 : (same_sign l_non_alias rsize_2 )) (PreH15 : (rcap_2 >= 0)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l_non_alias)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max (bn) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d_2 (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d_2 (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d_2 (Zabs (b__mp_size_2)) b__mp_alloc_2 )
  **  (UIntArray.undef_seg a__mp_d_2 (Zabs (a__mp_size_2)) a__mp_alloc_2 )
|--
  EX (b__mp_d: Z) (a__mp_d: Z) (r__mp_d: Z) (r__mp_alloc: Z) (rcap: Z) (rsize: Z) (a__mp_alloc: Z) (a__mp_size: Z) (b__mp_alloc: Z) (b__mp_size: Z),
  “ (cmp < 0) ”
  &&  “ (cmp <= 0) ”
  &&  “ ((Zabs (n_non_alias)) < (Zabs (m_non_alias))) ”
  &&  “ (cmp = (-1)) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ”
  &&  “ (r__mp_d = retval) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) ) ”
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_full retval bn )
  **  (UIntArray.undef_seg retval bn (Z.max ((Z.max (bn) (1))) (rcap)) )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b__mp_size_2: Z) (b__mp_alloc_2: Z) (an: Z) (a__mp_size_2: Z) (a__mp_alloc_2: Z) (a__mp_d_2: Z) (b__mp_d_2: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l_non_alias rsize_2 )) (PreH2 : (z__mp_alloc = (Z.max (bn) (rcap_2)))) (PreH3 : (cmp < 0)) (PreH4 : (cmp <= 0)) (PreH5 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH6 : (cmp = (-1))) (PreH7 : (bn = (Zabs (b__mp_size_2)))) (PreH8 : (same_sign m_non_alias b__mp_size_2 )) (PreH9 : ((Zabs (b__mp_size_2)) <= b__mp_alloc_2)) (PreH10 : (an = (Zabs (a__mp_size_2)))) (PreH11 : (same_sign n_non_alias a__mp_size_2 )) (PreH12 : ((Zabs (a__mp_size_2)) <= a__mp_alloc_2)) (PreH13 : ((Zabs (rsize_2)) <= rcap_2)) (PreH14 : (same_sign l_non_alias rsize_2 )) (PreH15 : (rcap_2 >= 0)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l_non_alias)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max (bn) (rcap_2)) )
  **  (mpd_store_Z_compact UINT_MOD a__mp_d_2 (Zabs (n_non_alias)) an )
  **  (mpd_store_Z_compact UINT_MOD b__mp_d_2 (Zabs (m_non_alias)) bn )
|--
  EX (rcap: Z),
  “ (z__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ”
  &&  “ (z__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ”
  &&  “ (cmp < 0) ”
  &&  “ (cmp <= 0) ”
  &&  “ ((Zabs (n_non_alias)) < (Zabs (m_non_alias))) ”
  &&  “ (cmp = (-1)) ”
  &&  “ (bn = (Zabs (b__mp_size_2))) ”
  &&  “ (same_sign m_non_alias b__mp_size_2 ) ”
  &&  “ ((Zabs (b__mp_size_2)) <= b__mp_alloc_2) ”
  &&  “ (an = (Zabs (a__mp_size_2))) ”
  &&  “ (same_sign n_non_alias a__mp_size_2 ) ”
  &&  “ ((Zabs (a__mp_size_2)) <= a__mp_alloc_2) ”
  &&  “ (same_sign l_non_alias rsize_2 ) ”
  &&  “ ((Zabs (rsize_2)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize_2)) ) ”
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD a__mp_d_2 (Zabs (n_non_alias)) an )
  **  (mpd_store_Z_compact UINT_MOD b__mp_d_2 (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_full retval bn )
  **  (UIntArray.undef_seg retval bn (Z.max ((Z.max (bn) (1))) (rcap)) )
).

Definition mpz_abs_sub_entail_wit_15_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign za_r_eq_a rsize )) (PreH2 : (z__mp_alloc = (Z.max (bn) (rcap)))) (PreH3 : (0 <= rcap)) (PreH4 : (rcap <= INT_MAX)) (PreH5 : (0 <= an)) (PreH6 : (an <= INT_MAX)) (PreH7 : (bn >= INT_MIN)) (PreH8 : (1 <= bn)) (PreH9 : (bn <= INT_MAX)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (rsize <= INT_MAX)) (PreH13 : (an <= INT_MAX)) (PreH14 : (cmp <= INT_MAX)) (PreH15 : (bcap >= INT_MIN)) (PreH16 : (bsize >= INT_MIN)) (PreH17 : (rcap >= INT_MIN)) (PreH18 : (rsize >= INT_MIN)) (PreH19 : (an >= INT_MIN)) (PreH20 : (cmp >= INT_MIN)) (PreH21 : (cmp < 0)) (PreH22 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH23 : (cmp = (-1))) (PreH24 : (an = (Zabs (rsize)))) (PreH25 : (bn = (Zabs (bsize)))) (PreH26 : (same_sign za_r_eq_a rsize )) (PreH27 : (same_sign zb_r_eq_a bsize )) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (0 <= rcap)) (PreH30 : (rcap <= INT_MAX)) (PreH31 : ((Zabs (bsize)) <= bcap)) (PreH32 : (r_pre = a_pre)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max (bn) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  EX (rcap_new: Z),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (z__mp_alloc: Z) (retval: Z) (PreH1 : (z__mp_alloc <= INT_MAX)) (PreH2 : (z__mp_alloc >= INT_MIN)) (PreH3 : (same_sign za_r_eq_a rsize )) (PreH4 : (z__mp_alloc = (Z.max (bn) (rcap)))) (PreH5 : (0 <= rcap)) (PreH6 : (rcap <= INT_MAX)) (PreH7 : (0 <= an)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bn >= INT_MIN)) (PreH10 : (1 <= bn)) (PreH11 : (bn <= INT_MAX)) (PreH12 : (bcap <= INT_MAX)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (rsize <= INT_MAX)) (PreH15 : (an <= INT_MAX)) (PreH16 : (cmp <= INT_MAX)) (PreH17 : (bcap >= INT_MIN)) (PreH18 : (bsize >= INT_MIN)) (PreH19 : (rcap >= INT_MIN)) (PreH20 : (rsize >= INT_MIN)) (PreH21 : (an >= INT_MIN)) (PreH22 : (cmp >= INT_MIN)) (PreH23 : (cmp < 0)) (PreH24 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH25 : (cmp = (-1))) (PreH26 : (an = (Zabs (rsize)))) (PreH27 : (bn = (Zabs (bsize)))) (PreH28 : (same_sign za_r_eq_a rsize )) (PreH29 : (same_sign zb_r_eq_a bsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (0 <= rcap)) (PreH32 : (rcap <= INT_MAX)) (PreH33 : ((Zabs (bsize)) <= bcap)) (PreH34 : (r_pre = a_pre)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (za_r_eq_a)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize)) (Z.max (bn) (rcap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (zb_r_eq_a)) bn )
|--
  EX (rcap_new: Z),
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

Definition mpz_abs_sub_return_wit_1_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
|--
  (store_Z a_pre n_non_alias )
  **  (store_Z b_pre m_non_alias )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) 0 )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  (store_Z r_pre l_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) 0 )
).

Definition mpz_abs_sub_return_wit_1_non_alias_split_goal_spatial :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n_non_alias)) = (Zabs (m_non_alias)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m_non_alias size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n_non_alias size )) (PreH10 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  (store_Z r_pre l_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) 0 )
.

Definition mpz_abs_sub_return_wit_2_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (bsize)))) (PreH6 : (retval = (Zabs (rsize)))) (PreH7 : (r_pre = a_pre)) (PreH8 : (INT_MIN < rsize)) (PreH9 : (rsize <= INT_MAX)) (PreH10 : (INT_MIN < bsize)) (PreH11 : (bsize <= INT_MAX)) (PreH12 : (0 <= rcap)) (PreH13 : (rcap <= INT_MAX)) (PreH14 : (0 <= bcap)) (PreH15 : (bcap <= INT_MAX)) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (same_sign za_r_eq_a rsize )) (PreH18 : ((Zabs (bsize)) <= bcap)) (PreH19 : (same_sign zb_r_eq_a bsize )),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 >= 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = 0)) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_return_wit_2_r_eq_a_split_goal_spatial :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (rcap >= INT_MIN)) (PreH2 : (rsize >= INT_MIN)) (PreH3 : (retval_3 >= 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (za_r_eq_a)) = (Zabs (zb_r_eq_a)))) (PreH6 : (retval_3 = 0)) (PreH7 : (retval_2 = (Zabs (bsize)))) (PreH8 : (retval = (Zabs (rsize)))) (PreH9 : (r_pre = a_pre)) (PreH10 : (INT_MIN < rsize)) (PreH11 : (rsize <= INT_MAX)) (PreH12 : (INT_MIN < bsize)) (PreH13 : (bsize <= INT_MAX)) (PreH14 : (0 <= rcap)) (PreH15 : (rcap <= INT_MAX)) (PreH16 : (0 <= bcap)) (PreH17 : (bcap <= INT_MAX)) (PreH18 : ((Zabs (rsize)) <= rcap)) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : ((Zabs (bsize)) <= bcap)) (PreH21 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_return_wit_3_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH6 : (cmp < 0)) (PreH7 : (cmp <= 0)) (PreH8 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH9 : (cmp = (-1))) (PreH10 : (bn = (Zabs (b__mp_size)))) (PreH11 : (same_sign m_non_alias b__mp_size )) (PreH12 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH13 : (an = (Zabs (a__mp_size)))) (PreH14 : (same_sign n_non_alias a__mp_size )) (PreH15 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH16 : (same_sign l_non_alias rsize )) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (rcap >= 0)) (PreH19 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH20 : (r__mp_d = rp)) (PreH21 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH22 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (store_Z a_pre n_non_alias )
  **  (store_Z b_pre m_non_alias )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) (-retval) )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= bn)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH10 : (cmp < 0)) (PreH11 : (cmp <= 0)) (PreH12 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH13 : (cmp = (-1))) (PreH14 : (bn = (Zabs (b__mp_size)))) (PreH15 : (same_sign m_non_alias b__mp_size )) (PreH16 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH17 : (an = (Zabs (a__mp_size)))) (PreH18 : (same_sign n_non_alias a__mp_size )) (PreH19 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH20 : (same_sign l_non_alias rsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (rcap >= 0)) (PreH23 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH24 : (r__mp_d = rp)) (PreH25 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH26 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) (Zabs (b__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) (Zabs (a__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) (-retval) )
).

Definition mpz_abs_sub_return_wit_3_non_alias_split_goal_spatial :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= bn)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH10 : (cmp < 0)) (PreH11 : (cmp <= 0)) (PreH12 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH13 : (cmp = (-1))) (PreH14 : (bn = (Zabs (b__mp_size)))) (PreH15 : (same_sign m_non_alias b__mp_size )) (PreH16 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH17 : (an = (Zabs (a__mp_size)))) (PreH18 : (same_sign n_non_alias a__mp_size )) (PreH19 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH20 : (same_sign l_non_alias rsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (rcap >= 0)) (PreH23 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH24 : (r__mp_d = rp)) (PreH25 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH26 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) (Zabs (b__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) (Zabs (a__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) (-retval) )
.

Definition mpz_abs_sub_return_wit_4_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH6 : (cmp < 0)) (PreH7 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH8 : (cmp = (-1))) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (bn <= rcap_new)) (PreH18 : (a = r_pre)) (PreH19 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= bn)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp < 0)) (PreH10 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = (-1))) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (bn <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_return_wit_4_r_eq_a_split_goal_spatial :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= bn)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp < 0)) (PreH10 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = (-1))) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (bn <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_return_wit_5_non_alias :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= an)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH6 : (cmp > 0)) (PreH7 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH8 : (cmp = 1)) (PreH9 : (bn = (Zabs (b__mp_size)))) (PreH10 : (same_sign m_non_alias b__mp_size )) (PreH11 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH12 : (an = (Zabs (a__mp_size)))) (PreH13 : (same_sign n_non_alias a__mp_size )) (PreH14 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH15 : (same_sign l_non_alias rsize )) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (rcap >= 0)) (PreH18 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH19 : (r__mp_d = rp)) (PreH20 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH21 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (store_Z a_pre n_non_alias )
  **  (store_Z b_pre m_non_alias )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) retval )
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= an)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH10 : (cmp > 0)) (PreH11 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH12 : (cmp = 1)) (PreH13 : (bn = (Zabs (b__mp_size)))) (PreH14 : (same_sign m_non_alias b__mp_size )) (PreH15 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH16 : (an = (Zabs (a__mp_size)))) (PreH17 : (same_sign n_non_alias a__mp_size )) (PreH18 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH19 : (same_sign l_non_alias rsize )) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (rcap >= 0)) (PreH22 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH23 : (r__mp_d = rp)) (PreH24 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH25 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) (Zabs (b__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) (Zabs (a__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) retval )
).

Definition mpz_abs_sub_return_wit_5_non_alias_split_goal_spatial :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= an)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH10 : (cmp > 0)) (PreH11 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH12 : (cmp = 1)) (PreH13 : (bn = (Zabs (b__mp_size)))) (PreH14 : (same_sign m_non_alias b__mp_size )) (PreH15 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH16 : (an = (Zabs (a__mp_size)))) (PreH17 : (same_sign n_non_alias a__mp_size )) (PreH18 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH19 : (same_sign l_non_alias rsize )) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (rcap >= 0)) (PreH22 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH23 : (r__mp_d = rp)) (PreH24 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH25 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) (Zabs (b__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) (Zabs (a__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ) retval )
.

Definition mpz_abs_sub_return_wit_6_r_eq_a :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= an)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH6 : (cmp > 0)) (PreH7 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH8 : (cmp = 1)) (PreH9 : (an = (Zabs (rsize)))) (PreH10 : (bn = (Zabs (bsize)))) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : (same_sign zb_r_eq_a bsize )) (PreH13 : ((Zabs (rsize)) <= rcap_new)) (PreH14 : (0 <= rcap_new)) (PreH15 : (rcap_new <= INT_MAX)) (PreH16 : ((Zabs (bsize)) <= bcap)) (PreH17 : (an <= rcap_new)) (PreH18 : (a = r_pre)) (PreH19 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= an)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp > 0)) (PreH10 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = 1)) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (an <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_return_wit_6_r_eq_a_split_goal_spatial :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (rsize <= INT_MAX)) (PreH2 : (rcap_new >= INT_MIN)) (PreH3 : (rsize >= INT_MIN)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= an)) (PreH6 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH7 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH8 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH9 : (cmp > 0)) (PreH10 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH11 : (cmp = 1)) (PreH12 : (an = (Zabs (rsize)))) (PreH13 : (bn = (Zabs (bsize)))) (PreH14 : (same_sign za_r_eq_a rsize )) (PreH15 : (same_sign zb_r_eq_a bsize )) (PreH16 : ((Zabs (rsize)) <= rcap_new)) (PreH17 : (0 <= rcap_new)) (PreH18 : (rcap_new <= INT_MAX)) (PreH19 : ((Zabs (bsize)) <= bcap)) (PreH20 : (an <= rcap_new)) (PreH21 : (a = r_pre)) (PreH22 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_1_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z),
  (store_Z a_pre n_non_alias )
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign n_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
.

Definition mpz_abs_sub_partial_solve_wit_2_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n_non_alias size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign n_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_abs_sub_partial_solve_wit_2_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign n_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_sub_partial_solve_wit_2_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n_non_alias size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
  &&  “ (same_sign n_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
.

Definition mpz_abs_sub_partial_solve_wit_2_non_alias := mpz_abs_sub_partial_solve_wit_2_non_alias_pure -> mpz_abs_sub_partial_solve_wit_2_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_3_r_eq_a_pure :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (INT_MIN < rsize)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (INT_MIN < bsize)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (0 <= rcap)) (PreH7 : (rcap <= INT_MAX)) (PreH8 : (0 <= bcap)) (PreH9 : (bcap <= INT_MAX)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : ((Zabs (bsize)) <= bcap)) (PreH13 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_3_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (INT_MIN < rsize)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (INT_MIN < bsize)) (PreH5 : (bsize <= INT_MAX)) (PreH6 : (0 <= rcap)) (PreH7 : (rcap <= INT_MAX)) (PreH8 : (0 <= bcap)) (PreH9 : (bcap <= INT_MAX)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign za_r_eq_a rsize )) (PreH12 : ((Zabs (bsize)) <= bcap)) (PreH13 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_3_r_eq_a := mpz_abs_sub_partial_solve_wit_3_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_3_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_4_non_alias :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (same_sign n_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m_non_alias )
  **  (store_Z r_pre l_non_alias )
|--
  EX (ptr_2: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign m_non_alias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (same_sign n_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
.

Definition mpz_abs_sub_partial_solve_wit_5_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign m_non_alias size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (retval = (Zabs (size_2)))) (PreH4 : (same_sign n_non_alias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size_2 <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size_2 >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (same_sign m_non_alias size )) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (same_sign n_non_alias size_2 )) (PreH15 : ((Zabs (size_2)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_abs_sub_partial_solve_wit_5_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size_2 <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size_2 >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (same_sign m_non_alias size )) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (same_sign n_non_alias size_2 )) (PreH15 : ((Zabs (size_2)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign m_non_alias size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (retval = (Zabs (size_2)))) (PreH4 : (same_sign n_non_alias size_2 )) (PreH5 : ((Zabs (size_2)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
  &&  “ (same_sign m_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap_2) ”
  &&  “ (retval = (Zabs (size_2))) ”
  &&  “ (same_sign n_non_alias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
.

Definition mpz_abs_sub_partial_solve_wit_5_non_alias := mpz_abs_sub_partial_solve_wit_5_non_alias_pure -> mpz_abs_sub_partial_solve_wit_5_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_6_r_eq_a_pure :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (PreH1 : (retval = (Zabs (rsize)))) (PreH2 : (r_pre = a_pre)) (PreH3 : (INT_MIN < rsize)) (PreH4 : (rsize <= INT_MAX)) (PreH5 : (INT_MIN < bsize)) (PreH6 : (bsize <= INT_MAX)) (PreH7 : (0 <= rcap)) (PreH8 : (rcap <= INT_MAX)) (PreH9 : (0 <= bcap)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_6_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (PreH1 : (retval = (Zabs (rsize)))) (PreH2 : (r_pre = a_pre)) (PreH3 : (INT_MIN < rsize)) (PreH4 : (rsize <= INT_MAX)) (PreH5 : (INT_MIN < bsize)) (PreH6 : (bsize <= INT_MAX)) (PreH7 : (0 <= rcap)) (PreH8 : (rcap <= INT_MAX)) (PreH9 : (0 <= bcap)) (PreH10 : (bcap <= INT_MAX)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign za_r_eq_a rsize )) (PreH13 : ((Zabs (bsize)) <= bcap)) (PreH14 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_6_r_eq_a := mpz_abs_sub_partial_solve_wit_6_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_6_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_7_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (same_sign m_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign n_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (retval_2 >= 0) ”
  &&  “ (retval >= 0) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m_non_alias size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n_non_alias size )) (PreH18 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (retval >= 0) ”
  &&  “ (retval_2 >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m_non_alias size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n_non_alias size )) (PreH18 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (retval >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_2 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (cap >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m_non_alias size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n_non_alias size )) (PreH18 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z r_pre l_non_alias )
|--
  “ (retval_2 >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (same_sign m_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign n_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
|--
  “ (retval_2 >= 0) ”
  &&  “ (retval >= 0) ”
  &&  “ (retval_2 = (Zabs (size_2))) ”
  &&  “ (same_sign m_non_alias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (same_sign n_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_non_alias)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_non_alias)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l_non_alias )
.

Definition mpz_abs_sub_partial_solve_wit_7_non_alias := mpz_abs_sub_partial_solve_wit_7_non_alias_pure -> mpz_abs_sub_partial_solve_wit_7_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (bsize)))) (PreH2 : (retval = (Zabs (rsize)))) (PreH3 : (r_pre = a_pre)) (PreH4 : (INT_MIN < rsize)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (INT_MIN < bsize)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (0 <= rcap)) (PreH9 : (rcap <= INT_MAX)) (PreH10 : (0 <= bcap)) (PreH11 : (bcap <= INT_MAX)) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (same_sign za_r_eq_a rsize )) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (same_sign zb_r_eq_a bsize )),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval_2 = (Zabs (bsize)))) (PreH10 : (retval = (Zabs (rsize)))) (PreH11 : (r_pre = a_pre)) (PreH12 : (INT_MIN < rsize)) (PreH13 : (rsize <= INT_MAX)) (PreH14 : (INT_MIN < bsize)) (PreH15 : (bsize <= INT_MAX)) (PreH16 : (0 <= rcap)) (PreH17 : (rcap <= INT_MAX)) (PreH18 : (0 <= bcap)) (PreH19 : (bcap <= INT_MAX)) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (same_sign za_r_eq_a rsize )) (PreH22 : ((Zabs (bsize)) <= bcap)) (PreH23 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval_2 = (Zabs (bsize)))) (PreH10 : (retval = (Zabs (rsize)))) (PreH11 : (r_pre = a_pre)) (PreH12 : (INT_MIN < rsize)) (PreH13 : (rsize <= INT_MAX)) (PreH14 : (INT_MIN < bsize)) (PreH15 : (bsize <= INT_MAX)) (PreH16 : (0 <= rcap)) (PreH17 : (rcap <= INT_MAX)) (PreH18 : (0 <= bcap)) (PreH19 : (bcap <= INT_MAX)) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (same_sign za_r_eq_a rsize )) (PreH22 : ((Zabs (bsize)) <= bcap)) (PreH23 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (bcap >= INT_MIN)) (PreH4 : (bsize >= INT_MIN)) (PreH5 : (rcap >= INT_MIN)) (PreH6 : (rsize >= INT_MIN)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (retval_2 >= INT_MIN)) (PreH9 : (retval_2 = (Zabs (bsize)))) (PreH10 : (retval = (Zabs (rsize)))) (PreH11 : (r_pre = a_pre)) (PreH12 : (INT_MIN < rsize)) (PreH13 : (rsize <= INT_MAX)) (PreH14 : (INT_MIN < bsize)) (PreH15 : (bsize <= INT_MAX)) (PreH16 : (0 <= rcap)) (PreH17 : (rcap <= INT_MAX)) (PreH18 : (0 <= bcap)) (PreH19 : (bcap <= INT_MAX)) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (same_sign za_r_eq_a rsize )) (PreH22 : ((Zabs (bsize)) <= bcap)) (PreH23 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_8_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (bsize)))) (PreH2 : (retval = (Zabs (rsize)))) (PreH3 : (r_pre = a_pre)) (PreH4 : (INT_MIN < rsize)) (PreH5 : (rsize <= INT_MAX)) (PreH6 : (INT_MIN < bsize)) (PreH7 : (bsize <= INT_MAX)) (PreH8 : (0 <= rcap)) (PreH9 : (rcap <= INT_MAX)) (PreH10 : (0 <= bcap)) (PreH11 : (bcap <= INT_MAX)) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (same_sign za_r_eq_a rsize )) (PreH14 : ((Zabs (bsize)) <= bcap)) (PreH15 : (same_sign zb_r_eq_a bsize )),
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

Definition mpz_abs_sub_partial_solve_wit_8_r_eq_a := mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_8_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_9_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b__mp_size)))) (PreH5 : (same_sign m_non_alias b__mp_size )) (PreH6 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH7 : (an = (Zabs (a__mp_size)))) (PreH8 : (same_sign n_non_alias a__mp_size )) (PreH9 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign l_non_alias rsize )) (PreH12 : (rcap >= 0)),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (rcap >= 0) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (an <= INT_MAX) ”
  &&  “ (an >= 0) ”
  &&  “ (rcap <= INT_MAX) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b__mp_size)))) (PreH23 : (same_sign m_non_alias b__mp_size )) (PreH24 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH25 : (an = (Zabs (a__mp_size)))) (PreH26 : (same_sign n_non_alias a__mp_size )) (PreH27 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (same_sign l_non_alias rsize )) (PreH30 : (rcap >= 0)),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (an >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_9_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b__mp_size)))) (PreH23 : (same_sign m_non_alias b__mp_size )) (PreH24 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH25 : (an = (Zabs (a__mp_size)))) (PreH26 : (same_sign n_non_alias a__mp_size )) (PreH27 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (same_sign l_non_alias rsize )) (PreH30 : (rcap >= 0)),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (an >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_9_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b__mp_size)))) (PreH5 : (same_sign m_non_alias b__mp_size )) (PreH6 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH7 : (an = (Zabs (a__mp_size)))) (PreH8 : (same_sign n_non_alias a__mp_size )) (PreH9 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign l_non_alias rsize )) (PreH12 : (rcap >= 0)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (an <= INT_MAX) ”
  &&  “ (an >= 0) ”
  &&  “ (rcap <= INT_MAX) ”
  &&  “ (cmp > 0) ”
  &&  “ ((Zabs (n_non_alias)) > (Zabs (m_non_alias))) ”
  &&  “ (cmp = 1) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
.

Definition mpz_abs_sub_partial_solve_wit_9_non_alias := mpz_abs_sub_partial_solve_wit_9_non_alias_pure -> mpz_abs_sub_partial_solve_wit_9_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_10_r_eq_a_pure :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= bn)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an >= INT_MIN)) (PreH6 : (1 <= an)) (PreH7 : (an <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (bn <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = 1)) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)),
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
  &&  “ (an >= 0) ”
  &&  “ (an <= INT_MAX) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign za_r_eq_a rsize ) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= bn)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an >= INT_MIN)) (PreH6 : (1 <= an)) (PreH7 : (an <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (bn <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = 1)) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)),
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
  &&  “ (an >= 0) ”
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

Definition mpz_abs_sub_partial_solve_wit_10_r_eq_a := mpz_abs_sub_partial_solve_wit_10_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_10_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_11_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b__mp_size)))) (PreH5 : (same_sign m_non_alias b__mp_size )) (PreH6 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH7 : (an = (Zabs (a__mp_size)))) (PreH8 : (same_sign n_non_alias a__mp_size )) (PreH9 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH10 : (same_sign l_non_alias rsize )) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (rcap >= 0)) (PreH13 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH14 : (r__mp_d = rp)) (PreH15 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH16 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (bn >= 0) ”
  &&  “ (an > 0) ”
  &&  “ (an >= bn) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b__mp_size)))) (PreH23 : (same_sign m_non_alias b__mp_size )) (PreH24 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH25 : (an = (Zabs (a__mp_size)))) (PreH26 : (same_sign n_non_alias a__mp_size )) (PreH27 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH28 : (same_sign l_non_alias rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ”
  &&  “ (an > 0) ”
  &&  “ (bn >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b__mp_size)))) (PreH23 : (same_sign m_non_alias b__mp_size )) (PreH24 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH25 : (an = (Zabs (a__mp_size)))) (PreH26 : (same_sign n_non_alias a__mp_size )) (PreH27 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH28 : (same_sign l_non_alias rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ”
.

Definition mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_2 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b__mp_size)))) (PreH23 : (same_sign m_non_alias b__mp_size )) (PreH24 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH25 : (an = (Zabs (a__mp_size)))) (PreH26 : (same_sign n_non_alias a__mp_size )) (PreH27 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH28 : (same_sign l_non_alias rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_3 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b__mp_size)))) (PreH23 : (same_sign m_non_alias b__mp_size )) (PreH24 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH25 : (an = (Zabs (a__mp_size)))) (PreH26 : (same_sign n_non_alias a__mp_size )) (PreH27 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH28 : (same_sign l_non_alias rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (bn >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_11_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b__mp_size)))) (PreH5 : (same_sign m_non_alias b__mp_size )) (PreH6 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH7 : (an = (Zabs (a__mp_size)))) (PreH8 : (same_sign n_non_alias a__mp_size )) (PreH9 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH10 : (same_sign l_non_alias rsize )) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (rcap >= 0)) (PreH13 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH14 : (r__mp_d = rp)) (PreH15 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH16 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (bn >= 0) ”
  &&  “ (an > 0) ”
  &&  “ (an >= bn) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn ) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an ) ”
  &&  “ (cmp > 0) ”
  &&  “ ((Zabs (n_non_alias)) > (Zabs (m_non_alias))) ”
  &&  “ (cmp = 1) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ”
  &&  “ (r__mp_d = rp) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) ) ”
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_full rp an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_11_non_alias := mpz_abs_sub_partial_solve_wit_11_non_alias_pure -> mpz_abs_sub_partial_solve_wit_11_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = 1)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (an <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_2 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_3 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp > 0)) (PreH15 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = 1)) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (an <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_12_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = 1)) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (an <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_12_r_eq_a := mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_12_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_13_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH4 : (cmp > 0)) (PreH5 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH6 : (cmp = 1)) (PreH7 : (bn = (Zabs (b__mp_size)))) (PreH8 : (same_sign m_non_alias b__mp_size )) (PreH9 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH10 : (an = (Zabs (a__mp_size)))) (PreH11 : (same_sign n_non_alias a__mp_size )) (PreH12 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH13 : (same_sign l_non_alias rsize )) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (rcap >= 0)) (PreH16 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH17 : (r__mp_d = rp)) (PreH18 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH19 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH22 : (cmp > 0)) (PreH23 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH24 : (cmp = 1)) (PreH25 : (bn = (Zabs (b__mp_size)))) (PreH26 : (same_sign m_non_alias b__mp_size )) (PreH27 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH28 : (an = (Zabs (a__mp_size)))) (PreH29 : (same_sign n_non_alias a__mp_size )) (PreH30 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH31 : (same_sign l_non_alias rsize )) (PreH32 : ((Zabs (rsize)) <= rcap)) (PreH33 : (rcap >= 0)) (PreH34 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH35 : (r__mp_d = rp)) (PreH36 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH37 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ”
).

Definition mpz_abs_sub_partial_solve_wit_13_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH22 : (cmp > 0)) (PreH23 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH24 : (cmp = 1)) (PreH25 : (bn = (Zabs (b__mp_size)))) (PreH26 : (same_sign m_non_alias b__mp_size )) (PreH27 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH28 : (an = (Zabs (a__mp_size)))) (PreH29 : (same_sign n_non_alias a__mp_size )) (PreH30 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH31 : (same_sign l_non_alias rsize )) (PreH32 : ((Zabs (rsize)) <= rcap)) (PreH33 : (rcap >= 0)) (PreH34 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH35 : (r__mp_d = rp)) (PreH36 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH37 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ”
.

Definition mpz_abs_sub_partial_solve_wit_13_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH4 : (cmp > 0)) (PreH5 : ((Zabs (n_non_alias)) > (Zabs (m_non_alias)))) (PreH6 : (cmp = 1)) (PreH7 : (bn = (Zabs (b__mp_size)))) (PreH8 : (same_sign m_non_alias b__mp_size )) (PreH9 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH10 : (an = (Zabs (a__mp_size)))) (PreH11 : (same_sign n_non_alias a__mp_size )) (PreH12 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH13 : (same_sign l_non_alias rsize )) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (rcap >= 0)) (PreH16 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH17 : (r__mp_d = rp)) (PreH18 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH19 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ”
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_non_alias)) - (Zabs (m_non_alias)) )) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn ) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an ) ”
  &&  “ (cmp > 0) ”
  &&  “ ((Zabs (n_non_alias)) > (Zabs (m_non_alias))) ”
  &&  “ (cmp = 1) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ”
  &&  “ (r__mp_d = rp) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) ) ”
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_13_non_alias := mpz_abs_sub_partial_solve_wit_13_non_alias_pure -> mpz_abs_sub_partial_solve_wit_13_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp > 0)) (PreH6 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = 1)) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (an <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp > 0)) (PreH18 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = 1)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (an <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp > 0)) (PreH18 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = 1)) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (an <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_14_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (za_r_eq_a)) - (Zabs (zb_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp > 0)) (PreH6 : ((Zabs (za_r_eq_a)) > (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = 1)) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (an <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_14_r_eq_a := mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_14_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_15_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b__mp_size)))) (PreH6 : (same_sign m_non_alias b__mp_size )) (PreH7 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH8 : (an = (Zabs (a__mp_size)))) (PreH9 : (same_sign n_non_alias a__mp_size )) (PreH10 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign l_non_alias rsize )) (PreH13 : (rcap >= 0)),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (rcap >= 0) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (bn <= INT_MAX) ”
  &&  “ (bn >= 0) ”
  &&  “ (rcap <= INT_MAX) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b__mp_size)))) (PreH24 : (same_sign m_non_alias b__mp_size )) (PreH25 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH26 : (an = (Zabs (a__mp_size)))) (PreH27 : (same_sign n_non_alias a__mp_size )) (PreH28 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (same_sign l_non_alias rsize )) (PreH31 : (rcap >= 0)),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (bn >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_15_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b__mp_size)))) (PreH24 : (same_sign m_non_alias b__mp_size )) (PreH25 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH26 : (an = (Zabs (a__mp_size)))) (PreH27 : (same_sign n_non_alias a__mp_size )) (PreH28 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (same_sign l_non_alias rsize )) (PreH31 : (rcap >= 0)),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (bn >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_15_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b__mp_size)))) (PreH6 : (same_sign m_non_alias b__mp_size )) (PreH7 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH8 : (an = (Zabs (a__mp_size)))) (PreH9 : (same_sign n_non_alias a__mp_size )) (PreH10 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign l_non_alias rsize )) (PreH13 : (rcap >= 0)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (bn <= INT_MAX) ”
  &&  “ (bn >= 0) ”
  &&  “ (rcap <= INT_MAX) ”
  &&  “ (cmp < 0) ”
  &&  “ (cmp <= 0) ”
  &&  “ ((Zabs (n_non_alias)) < (Zabs (m_non_alias))) ”
  &&  “ (cmp = (-1)) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l_non_alias)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
.

Definition mpz_abs_sub_partial_solve_wit_15_non_alias := mpz_abs_sub_partial_solve_wit_15_non_alias_pure -> mpz_abs_sub_partial_solve_wit_15_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_16_r_eq_a_pure :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= an)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn >= INT_MIN)) (PreH6 : (1 <= bn)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (an <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (an >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = (-1))) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)),
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
  &&  “ (bn >= 0) ”
  &&  “ (bn <= INT_MAX) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (same_sign za_r_eq_a rsize ) ”
.

Definition mpz_abs_sub_partial_solve_wit_16_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rptr: Z) (rsize: Z) (rcap: Z) (bptr: Z) (bsize: Z) (bcap: Z) (cmp: Z) (an: Z) (bn: Z) (PreH1 : (0 <= rcap)) (PreH2 : (rcap <= INT_MAX)) (PreH3 : (0 <= an)) (PreH4 : (an <= INT_MAX)) (PreH5 : (bn >= INT_MIN)) (PreH6 : (1 <= bn)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (bcap <= INT_MAX)) (PreH9 : (bsize <= INT_MAX)) (PreH10 : (rsize <= INT_MAX)) (PreH11 : (an <= INT_MAX)) (PreH12 : (cmp <= INT_MAX)) (PreH13 : (bcap >= INT_MIN)) (PreH14 : (bsize >= INT_MIN)) (PreH15 : (rcap >= INT_MIN)) (PreH16 : (rsize >= INT_MIN)) (PreH17 : (an >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH21 : (cmp = (-1))) (PreH22 : (an = (Zabs (rsize)))) (PreH23 : (bn = (Zabs (bsize)))) (PreH24 : (same_sign za_r_eq_a rsize )) (PreH25 : (same_sign zb_r_eq_a bsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (0 <= rcap)) (PreH28 : (rcap <= INT_MAX)) (PreH29 : ((Zabs (bsize)) <= bcap)) (PreH30 : (r_pre = a_pre)),
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
  &&  “ (bn >= 0) ”
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

Definition mpz_abs_sub_partial_solve_wit_16_r_eq_a := mpz_abs_sub_partial_solve_wit_16_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_16_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_17_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b__mp_size)))) (PreH6 : (same_sign m_non_alias b__mp_size )) (PreH7 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH8 : (an = (Zabs (a__mp_size)))) (PreH9 : (same_sign n_non_alias a__mp_size )) (PreH10 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH11 : (same_sign l_non_alias rsize )) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (rcap >= 0)) (PreH14 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH15 : (r__mp_d = rp)) (PreH16 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH17 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (an >= 0) ”
  &&  “ (bn > 0) ”
  &&  “ (bn >= an) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b__mp_size)))) (PreH24 : (same_sign m_non_alias b__mp_size )) (PreH25 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH26 : (an = (Zabs (a__mp_size)))) (PreH27 : (same_sign n_non_alias a__mp_size )) (PreH28 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH29 : (same_sign l_non_alias rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ”
  &&  “ (bn > 0) ”
  &&  “ (an >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b__mp_size)))) (PreH24 : (same_sign m_non_alias b__mp_size )) (PreH25 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH26 : (an = (Zabs (a__mp_size)))) (PreH27 : (same_sign n_non_alias a__mp_size )) (PreH28 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH29 : (same_sign l_non_alias rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ”
.

Definition mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_2 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b__mp_size)))) (PreH24 : (same_sign m_non_alias b__mp_size )) (PreH25 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH26 : (an = (Zabs (a__mp_size)))) (PreH27 : (same_sign n_non_alias a__mp_size )) (PreH28 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH29 : (same_sign l_non_alias rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_3 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b__mp_size)))) (PreH24 : (same_sign m_non_alias b__mp_size )) (PreH25 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH26 : (an = (Zabs (a__mp_size)))) (PreH27 : (same_sign n_non_alias a__mp_size )) (PreH28 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH29 : (same_sign l_non_alias rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (an >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_17_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b__mp_size)))) (PreH6 : (same_sign m_non_alias b__mp_size )) (PreH7 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH8 : (an = (Zabs (a__mp_size)))) (PreH9 : (same_sign n_non_alias a__mp_size )) (PreH10 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH11 : (same_sign l_non_alias rsize )) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (rcap >= 0)) (PreH14 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH15 : (r__mp_d = rp)) (PreH16 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH17 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (an >= 0) ”
  &&  “ (bn > 0) ”
  &&  “ (bn >= an) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn ) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an ) ”
  &&  “ (cmp < 0) ”
  &&  “ (cmp <= 0) ”
  &&  “ ((Zabs (n_non_alias)) < (Zabs (m_non_alias))) ”
  &&  “ (cmp = (-1)) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ”
  &&  “ (r__mp_d = rp) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) ) ”
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (UIntArray.undef_full rp bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_17_non_alias := mpz_abs_sub_partial_solve_wit_17_non_alias_pure -> mpz_abs_sub_partial_solve_wit_17_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp < 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = (-1))) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (bn <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_2 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_3 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (cmp < 0)) (PreH15 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH16 : (cmp = (-1))) (PreH17 : (an = (Zabs (rsize)))) (PreH18 : (bn = (Zabs (bsize)))) (PreH19 : (same_sign za_r_eq_a rsize )) (PreH20 : (same_sign zb_r_eq_a bsize )) (PreH21 : ((Zabs (rsize)) <= rcap_new)) (PreH22 : (0 <= rcap_new)) (PreH23 : (rcap_new <= INT_MAX)) (PreH24 : ((Zabs (bsize)) <= bcap)) (PreH25 : (bn <= rcap_new)) (PreH26 : (a = r_pre)) (PreH27 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_18_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (PreH1 : (cmp < 0)) (PreH2 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH3 : (cmp = (-1))) (PreH4 : (an = (Zabs (rsize)))) (PreH5 : (bn = (Zabs (bsize)))) (PreH6 : (same_sign za_r_eq_a rsize )) (PreH7 : (same_sign zb_r_eq_a bsize )) (PreH8 : ((Zabs (rsize)) <= rcap_new)) (PreH9 : (0 <= rcap_new)) (PreH10 : (rcap_new <= INT_MAX)) (PreH11 : ((Zabs (bsize)) <= bcap)) (PreH12 : (bn <= rcap_new)) (PreH13 : (a = r_pre)) (PreH14 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_18_r_eq_a := mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_18_r_eq_a_aux.

Definition mpz_abs_sub_partial_solve_wit_19_non_alias_pure :=
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH4 : (cmp < 0)) (PreH5 : (cmp <= 0)) (PreH6 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH7 : (cmp = (-1))) (PreH8 : (bn = (Zabs (b__mp_size)))) (PreH9 : (same_sign m_non_alias b__mp_size )) (PreH10 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH11 : (an = (Zabs (a__mp_size)))) (PreH12 : (same_sign n_non_alias a__mp_size )) (PreH13 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH14 : (same_sign l_non_alias rsize )) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (rcap >= 0)) (PreH17 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH18 : (r__mp_d = rp)) (PreH19 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH20 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ”
) \/
(
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH22 : (cmp < 0)) (PreH23 : (cmp <= 0)) (PreH24 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH25 : (cmp = (-1))) (PreH26 : (bn = (Zabs (b__mp_size)))) (PreH27 : (same_sign m_non_alias b__mp_size )) (PreH28 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH29 : (an = (Zabs (a__mp_size)))) (PreH30 : (same_sign n_non_alias a__mp_size )) (PreH31 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH32 : (same_sign l_non_alias rsize )) (PreH33 : ((Zabs (rsize)) <= rcap)) (PreH34 : (rcap >= 0)) (PreH35 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH36 : (r__mp_d = rp)) (PreH37 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH38 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ”
).

Definition mpz_abs_sub_partial_solve_wit_19_non_alias_pure_split_goal_1 :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a__mp_alloc <= INT_MAX)) (PreH4 : (a__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b__mp_alloc <= INT_MAX)) (PreH7 : (b__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a__mp_alloc >= INT_MIN)) (PreH13 : (a__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b__mp_alloc >= INT_MIN)) (PreH16 : (b__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH22 : (cmp < 0)) (PreH23 : (cmp <= 0)) (PreH24 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH25 : (cmp = (-1))) (PreH26 : (bn = (Zabs (b__mp_size)))) (PreH27 : (same_sign m_non_alias b__mp_size )) (PreH28 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH29 : (an = (Zabs (a__mp_size)))) (PreH30 : (same_sign n_non_alias a__mp_size )) (PreH31 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH32 : (same_sign l_non_alias rsize )) (PreH33 : ((Zabs (rsize)) <= rcap)) (PreH34 : (rcap >= 0)) (PreH35 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH36 : (r__mp_d = rp)) (PreH37 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH38 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ”
.

Definition mpz_abs_sub_partial_solve_wit_19_non_alias_aux :=
forall (l_non_alias: Z) (m_non_alias: Z) (n_non_alias: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b__mp_size: Z) (b__mp_alloc: Z) (an: Z) (a__mp_size: Z) (a__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a__mp_d: Z) (b__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an )) (PreH4 : (cmp < 0)) (PreH5 : (cmp <= 0)) (PreH6 : ((Zabs (n_non_alias)) < (Zabs (m_non_alias)))) (PreH7 : (cmp = (-1))) (PreH8 : (bn = (Zabs (b__mp_size)))) (PreH9 : (same_sign m_non_alias b__mp_size )) (PreH10 : ((Zabs (b__mp_size)) <= b__mp_alloc)) (PreH11 : (an = (Zabs (a__mp_size)))) (PreH12 : (same_sign n_non_alias a__mp_size )) (PreH13 : ((Zabs (a__mp_size)) <= a__mp_alloc)) (PreH14 : (same_sign l_non_alias rsize )) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (rcap >= 0)) (PreH17 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH18 : (r__mp_d = rp)) (PreH19 : (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) )) (PreH20 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))),
  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ”
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m_non_alias)) - (Zabs (n_non_alias)) )) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_non_alias)) bn ) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_non_alias)) an ) ”
  &&  “ (cmp < 0) ”
  &&  “ (cmp <= 0) ”
  &&  “ ((Zabs (n_non_alias)) < (Zabs (m_non_alias))) ”
  &&  “ (cmp = (-1)) ”
  &&  “ (bn = (Zabs (b__mp_size))) ”
  &&  “ (same_sign m_non_alias b__mp_size ) ”
  &&  “ ((Zabs (b__mp_size)) <= b__mp_alloc) ”
  &&  “ (an = (Zabs (a__mp_size))) ”
  &&  “ (same_sign n_non_alias a__mp_size ) ”
  &&  “ ((Zabs (a__mp_size)) <= a__mp_alloc) ”
  &&  “ (same_sign l_non_alias rsize ) ”
  &&  “ ((Zabs (rsize)) <= rcap) ”
  &&  “ (rcap >= 0) ”
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ”
  &&  “ (r__mp_d = rp) ”
  &&  “ (is_compact_Z UINT_MOD (Zabs (l_non_alias)) (Zabs (rsize)) ) ”
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  (mpd_store_Z UINT_MOD b__mp_d (Zabs (m_non_alias)) bn )
  **  (mpd_store_Z UINT_MOD a__mp_d (Zabs (n_non_alias)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b__mp_d)
  **  (UIntArray.undef_seg b__mp_d (Zabs (b__mp_size)) b__mp_alloc )
  **  (UIntArray.undef_seg a__mp_d (Zabs (a__mp_size)) a__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_19_non_alias := mpz_abs_sub_partial_solve_wit_19_non_alias_pure -> mpz_abs_sub_partial_solve_wit_19_non_alias_aux.

Definition mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure :=
(
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp < 0)) (PreH6 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = (-1))) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (bn <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)),
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
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp < 0)) (PreH18 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = (-1))) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (bn <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure_split_goal_1 :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (rsize <= INT_MAX)) (PreH4 : (bn <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (cmp <= INT_MAX)) (PreH7 : (bcap >= INT_MIN)) (PreH8 : (bsize >= INT_MIN)) (PreH9 : (rcap_new >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bn >= INT_MIN)) (PreH12 : (an >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH15 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH16 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH17 : (cmp < 0)) (PreH18 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH19 : (cmp = (-1))) (PreH20 : (an = (Zabs (rsize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (same_sign za_r_eq_a rsize )) (PreH23 : (same_sign zb_r_eq_a bsize )) (PreH24 : ((Zabs (rsize)) <= rcap_new)) (PreH25 : (0 <= rcap_new)) (PreH26 : (rcap_new <= INT_MAX)) (PreH27 : ((Zabs (bsize)) <= bcap)) (PreH28 : (bn <= rcap_new)) (PreH29 : (a = r_pre)) (PreH30 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_20_r_eq_a_aux :=
forall (zb_r_eq_a: Z) (za_r_eq_a: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (rsize: Z) (bptr: Z) (bsize: Z) (bcap: Z) (rptr_new: Z) (rcap_new: Z) (cmp: Z) (an: Z) (bn: Z) (a: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (zb_r_eq_a)) - (Zabs (za_r_eq_a)) ))) (PreH2 : (rptr_new = rptr_new)) (PreH3 : (is_compact_Z UINT_MOD (Zabs (zb_r_eq_a)) bn )) (PreH4 : (is_compact_Z UINT_MOD (Zabs (za_r_eq_a)) an )) (PreH5 : (cmp < 0)) (PreH6 : ((Zabs (za_r_eq_a)) < (Zabs (zb_r_eq_a)))) (PreH7 : (cmp = (-1))) (PreH8 : (an = (Zabs (rsize)))) (PreH9 : (bn = (Zabs (bsize)))) (PreH10 : (same_sign za_r_eq_a rsize )) (PreH11 : (same_sign zb_r_eq_a bsize )) (PreH12 : ((Zabs (rsize)) <= rcap_new)) (PreH13 : (0 <= rcap_new)) (PreH14 : (rcap_new <= INT_MAX)) (PreH15 : ((Zabs (bsize)) <= bcap)) (PreH16 : (bn <= rcap_new)) (PreH17 : (a = r_pre)) (PreH18 : (r_pre = a_pre)),
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

Definition mpz_abs_sub_partial_solve_wit_20_r_eq_a := mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure -> mpz_abs_sub_partial_solve_wit_20_r_eq_a_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_abs_sub_safety_wit_1_non_alias : mpz_abs_sub_safety_wit_1_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_2_non_alias : mpz_abs_sub_safety_wit_2_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_3_non_alias : mpz_abs_sub_safety_wit_3_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_4_r_eq_a : mpz_abs_sub_safety_wit_4_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_5_r_eq_a : mpz_abs_sub_safety_wit_5_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_6_r_eq_a : mpz_abs_sub_safety_wit_6_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_7_non_alias : mpz_abs_sub_safety_wit_7_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_8_non_alias : mpz_abs_sub_safety_wit_8_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_9_non_alias : mpz_abs_sub_safety_wit_9_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_10_r_eq_a : mpz_abs_sub_safety_wit_10_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_11_r_eq_a : mpz_abs_sub_safety_wit_11_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_12_r_eq_a : mpz_abs_sub_safety_wit_12_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_13_non_alias : mpz_abs_sub_safety_wit_13_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_14_non_alias : mpz_abs_sub_safety_wit_14_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_15_r_eq_a : mpz_abs_sub_safety_wit_15_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_16_r_eq_a : mpz_abs_sub_safety_wit_16_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_17_non_alias : mpz_abs_sub_safety_wit_17_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_18_non_alias : mpz_abs_sub_safety_wit_18_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_19_r_eq_a : mpz_abs_sub_safety_wit_19_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_20_r_eq_a : mpz_abs_sub_safety_wit_20_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_21_r_eq_a : mpz_abs_sub_safety_wit_21_r_eq_a.
Axiom proof_of_mpz_abs_sub_safety_wit_22_non_alias : mpz_abs_sub_safety_wit_22_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_23_non_alias : mpz_abs_sub_safety_wit_23_non_alias.
Axiom proof_of_mpz_abs_sub_safety_wit_24_r_eq_a : mpz_abs_sub_safety_wit_24_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_1_r_eq_a : mpz_abs_sub_entail_wit_1_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_2_r_eq_a : mpz_abs_sub_entail_wit_2_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_3_r_eq_a : mpz_abs_sub_entail_wit_3_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_4_r_eq_a : mpz_abs_sub_entail_wit_4_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_5_r_eq_a : mpz_abs_sub_entail_wit_5_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_6_non_alias : mpz_abs_sub_entail_wit_6_non_alias.
Axiom proof_of_mpz_abs_sub_entail_wit_7_non_alias : mpz_abs_sub_entail_wit_7_non_alias.
Axiom proof_of_mpz_abs_sub_entail_wit_8_r_eq_a : mpz_abs_sub_entail_wit_8_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_9_r_eq_a : mpz_abs_sub_entail_wit_9_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_10_r_eq_a : mpz_abs_sub_entail_wit_10_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_11_r_eq_a : mpz_abs_sub_entail_wit_11_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_12_r_eq_a : mpz_abs_sub_entail_wit_12_r_eq_a.
Axiom proof_of_mpz_abs_sub_entail_wit_13_non_alias : mpz_abs_sub_entail_wit_13_non_alias.
Axiom proof_of_mpz_abs_sub_entail_wit_14_non_alias : mpz_abs_sub_entail_wit_14_non_alias.
Axiom proof_of_mpz_abs_sub_entail_wit_15_r_eq_a : mpz_abs_sub_entail_wit_15_r_eq_a.
Axiom proof_of_mpz_abs_sub_return_wit_1_non_alias : mpz_abs_sub_return_wit_1_non_alias.
Axiom proof_of_mpz_abs_sub_return_wit_2_r_eq_a : mpz_abs_sub_return_wit_2_r_eq_a.
Axiom proof_of_mpz_abs_sub_return_wit_3_non_alias : mpz_abs_sub_return_wit_3_non_alias.
Axiom proof_of_mpz_abs_sub_return_wit_4_r_eq_a : mpz_abs_sub_return_wit_4_r_eq_a.
Axiom proof_of_mpz_abs_sub_return_wit_5_non_alias : mpz_abs_sub_return_wit_5_non_alias.
Axiom proof_of_mpz_abs_sub_return_wit_6_r_eq_a : mpz_abs_sub_return_wit_6_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_1_non_alias : mpz_abs_sub_partial_solve_wit_1_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2_non_alias_pure : mpz_abs_sub_partial_solve_wit_2_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2_non_alias : mpz_abs_sub_partial_solve_wit_2_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_3_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_3_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_3_r_eq_a : mpz_abs_sub_partial_solve_wit_3_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4_non_alias : mpz_abs_sub_partial_solve_wit_4_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5_non_alias_pure : mpz_abs_sub_partial_solve_wit_5_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5_non_alias : mpz_abs_sub_partial_solve_wit_5_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_6_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6_r_eq_a : mpz_abs_sub_partial_solve_wit_6_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias_pure : mpz_abs_sub_partial_solve_wit_7_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias : mpz_abs_sub_partial_solve_wit_7_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a : mpz_abs_sub_partial_solve_wit_8_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9_non_alias_pure : mpz_abs_sub_partial_solve_wit_9_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9_non_alias : mpz_abs_sub_partial_solve_wit_9_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_10_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_10_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_10_r_eq_a : mpz_abs_sub_partial_solve_wit_10_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure : mpz_abs_sub_partial_solve_wit_11_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias : mpz_abs_sub_partial_solve_wit_11_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a : mpz_abs_sub_partial_solve_wit_12_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_13_non_alias_pure : mpz_abs_sub_partial_solve_wit_13_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_13_non_alias : mpz_abs_sub_partial_solve_wit_13_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_14_r_eq_a : mpz_abs_sub_partial_solve_wit_14_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_15_non_alias_pure : mpz_abs_sub_partial_solve_wit_15_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_15_non_alias : mpz_abs_sub_partial_solve_wit_15_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_16_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_16_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_16_r_eq_a : mpz_abs_sub_partial_solve_wit_16_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure : mpz_abs_sub_partial_solve_wit_17_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias : mpz_abs_sub_partial_solve_wit_17_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a : mpz_abs_sub_partial_solve_wit_18_r_eq_a.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_19_non_alias_pure : mpz_abs_sub_partial_solve_wit_19_non_alias_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_19_non_alias : mpz_abs_sub_partial_solve_wit_19_non_alias.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_20_r_eq_a : mpz_abs_sub_partial_solve_wit_20_r_eq_a.

End VC_Correct.
