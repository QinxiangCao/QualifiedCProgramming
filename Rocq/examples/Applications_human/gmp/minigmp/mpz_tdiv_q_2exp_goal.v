From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_div_q_2exp -----*)

Definition mpz_div_q_2exp_safety_wit_1 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_2 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_3 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_div_q_2exp_safety_wit_4 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_div_q_2exp_safety_wit_5 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
).

Definition mpz_div_q_2exp_safety_wit_5_split_goal_1 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_div_q_2exp_safety_wit_5_split_goal_2 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
.

Definition mpz_div_q_2exp_safety_wit_6 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_div_q_2exp_safety_wit_7 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_div_q_2exp_safety_wit_8 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_9 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <> 0)) (PreH4 : (q_pre = u_pre)) (PreH5 : (mode_pre = 2)) (PreH6 : (bit_index_pre >= 0)) (PreH7 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_div_q_2exp_safety_wit_10 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size <= 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <> 0)) (PreH4 : (q_pre = u_pre)) (PreH5 : (mode_pre = 2)) (PreH6 : (bit_index_pre >= 0)) (PreH7 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_11 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre = 1)) (PreH2 : (size > 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_12 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre = 0)) (PreH2 : (size <= 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_13 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 1)) (PreH2 : (size > 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_14 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 0)) (PreH2 : (size <= 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_15 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 1)) (PreH2 : (size > 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_16 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 0)) (PreH2 : (size <= 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_17 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_18 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_19 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH5 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH6 : (bit_index >= 0)) (PreH7 : (bit_index < 32)) (PreH8 : (un <> 0)) (PreH9 : ((Zabs (un)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc un )) (PreH13 : (adjust = 0)) (PreH14 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH15 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH16 : (qn > 0)) (PreH17 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH18 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH19 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((last (l) (1)) >= 1)) (PreH22 : (u__mp_size = un)) (PreH23 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH24 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_20 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((qn - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (qn - 1 )) ”
.

Definition mpz_div_q_2exp_safety_wit_21 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((qn - 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (qn - 0 )) ”
.

Definition mpz_div_q_2exp_safety_wit_22 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((qn - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (qn - 1 )) ”
.

Definition mpz_div_q_2exp_safety_wit_23 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_div_q_2exp_safety_wit_24 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_25 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust <> 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_26 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust <> 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_27 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) (PreH26 : (adjust <> 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_28 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_29 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_30 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_31 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_32 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) (PreH26 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_33 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 1)) (PreH4 : (size > 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_34 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size >= 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 0)) (PreH4 : (size <= 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_entail_wit_1 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)),
  (store_Z q_pre z_eq_trunc )
|--
  EX (ptr: Z) (cap: Z) (size: Z),
  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)),
  (store_Z q_pre z_eq_trunc )
|--
  EX (ptr: Z) (cap: Z) (size: Z),
  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
).

Definition mpz_div_q_2exp_entail_wit_2_1 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (size: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq_trunc size )) (PreH2 : (z__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH4 : (mode_pre <> 1)) (PreH5 : (size > 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (cap_2 >= 0)) (PreH14 : (cap_2 <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z) (u__mp_alloc: Z) (u__mp_size: Z) (l: (@list Z)) (cap: Z),
  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((bit_index_pre % ( 32 ) ) = (bit_index_pre % ( 32 ) )) ”
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ”
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ”
  &&  “ (size <> 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ (0 = 0) ”
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ”
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ”
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = size) ”
  &&  “ (u__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap))) ”
  &&  “ (u__mp_d = retval_2) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (size: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (z__mp_alloc <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (z__mp_alloc >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign z_eq_trunc size )) (PreH6 : (z__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH7 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH8 : (mode_pre <> 1)) (PreH9 : (size > 0)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (size <> 0)) (PreH12 : (q_pre = u_pre)) (PreH13 : (mode_pre = 2)) (PreH14 : (bit_index_pre >= 0)) (PreH15 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH16 : ((Zabs (size)) <= cap_2)) (PreH17 : (cap_2 >= 0)) (PreH18 : (cap_2 <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc size )),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z)) (cap: Z),
  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ”
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ”
  &&  “ (size <> 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ”
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ”
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
).

Definition mpz_div_q_2exp_entail_wit_2_2 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (size: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq_trunc size )) (PreH2 : (z__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH4 : (mode_pre <> 0)) (PreH5 : (size <= 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (cap_2 >= 0)) (PreH14 : (cap_2 <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z) (u__mp_alloc: Z) (u__mp_size: Z) (l: (@list Z)) (cap: Z),
  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((bit_index_pre % ( 32 ) ) = (bit_index_pre % ( 32 ) )) ”
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ”
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ”
  &&  “ (size <> 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ (0 = 0) ”
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ”
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ”
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = size) ”
  &&  “ (u__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap))) ”
  &&  “ (u__mp_d = retval_2) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (size: Z) (cap_2: Z) (retval: Z) (z__mp_alloc: Z) (retval_2: Z) (PreH1 : (z__mp_alloc <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (z__mp_alloc >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign z_eq_trunc size )) (PreH6 : (z__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH7 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH8 : (mode_pre <> 0)) (PreH9 : (size <= 0)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (size <> 0)) (PreH12 : (q_pre = u_pre)) (PreH13 : (mode_pre = 2)) (PreH14 : (bit_index_pre >= 0)) (PreH15 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH16 : ((Zabs (size)) <= cap_2)) (PreH17 : (cap_2 >= 0)) (PreH18 : (cap_2 <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc size )),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z)) (cap: Z),
  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ”
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ”
  &&  “ (size <> 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ”
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ”
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
).

Definition mpz_div_q_2exp_entail_wit_3_1 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 0)) (PreH4 : (size <= 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (size < 0) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (cap >= INT_MIN)) (PreH2 : (size < 0)) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH4 : (mode_pre <> 0)) (PreH5 : (size <= 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap)) (PreH13 : (cap >= 0)) (PreH14 : (cap <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z) (ptr_2: Z),
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) 0 ) ”
  &&  “ ((Zabs (0)) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (size < 0) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs (0)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_entail_wit_3_2 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un < 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un < 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) (qn - 0 ) ) ”
  &&  “ ((Zabs ((qn - 0 ))) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 0 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 0 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_entail_wit_3_3 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un < 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un < 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) (qn - 1 ) ) ”
  &&  “ ((Zabs ((qn - 1 ))) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 1 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 1 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_entail_wit_3_4 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (un < 0)) (PreH2 : (bit_index = 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH8 : (bit_index >= 0)) (PreH9 : (bit_index < 32)) (PreH10 : (un <> 0)) (PreH11 : ((Zabs (un)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc un )) (PreH15 : (adjust = 0)) (PreH16 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH17 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH18 : (qn > 0)) (PreH19 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH20 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_size = un)) (PreH25 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH26 : (u__mp_d = qp)) (PreH27 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un < 0)) (PreH4 : (bit_index = 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH10 : (bit_index >= 0)) (PreH11 : (bit_index < 32)) (PreH12 : (un <> 0)) (PreH13 : ((Zabs (un)) <= cap)) (PreH14 : (cap >= 0)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (same_sign z_eq_trunc un )) (PreH17 : (adjust = 0)) (PreH18 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH19 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH20 : (qn > 0)) (PreH21 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH22 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH24 : (list_within_bound UINT_MOD l )) (PreH25 : ((last (l) (1)) >= 1)) (PreH26 : (u__mp_size = un)) (PreH27 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH28 : (u__mp_d = qp)) (PreH29 : (adjust = 0)),
  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) qn ) ”
  &&  “ ((Zabs (qn)) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (UIntArray.undef_seg ptr (Zabs (qn)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs (qn)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_1 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap >= INT_MIN)) (PreH2 : (size = 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z) (ptr_2: Z),
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) 0 ) ”
  &&  “ ((Zabs (0)) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs (0)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_2 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (un: Z) (PreH1 : (q_pre = q_pre)) (PreH2 : (q_pre = u_pre)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : (un < 0)) (PreH5 : (same_sign z_eq_trunc un )),
  (store_Z q_pre (-(Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre))))) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )),
  (store_Z q_pre (-(Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre))))) )
|--
  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
).

Definition mpz_div_q_2exp_return_wit_2_split_goal_spatial :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )),
  (store_Z q_pre (-(Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre))))) )
|--
  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
.

Definition mpz_div_q_2exp_return_wit_3 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size >= 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 1)) (PreH4 : (size > 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (cap >= INT_MIN)) (PreH2 : (size >= 0)) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH4 : (mode_pre <> 1)) (PreH5 : (size > 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap)) (PreH13 : (cap >= 0)) (PreH14 : (cap <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z) (ptr_2: Z),
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) 0 ) ”
  &&  “ ((Zabs (0)) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs (0)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_4 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un >= 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un >= 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) (qn - 0 ) ) ”
  &&  “ ((Zabs ((qn - 0 ))) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 0 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 0 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_5 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un >= 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un >= 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) (qn - 1 ) ) ”
  &&  “ ((Zabs ((qn - 1 ))) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 1 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 1 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_6 :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (un >= 0)) (PreH2 : (bit_index = 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH8 : (bit_index >= 0)) (PreH9 : (bit_index < 32)) (PreH10 : (un <> 0)) (PreH11 : ((Zabs (un)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc un )) (PreH15 : (adjust = 0)) (PreH16 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH17 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH18 : (qn > 0)) (PreH19 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH20 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_size = un)) (PreH25 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH26 : (u__mp_d = qp)) (PreH27 : (adjust = 0)),
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un >= 0)) (PreH4 : (bit_index = 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH10 : (bit_index >= 0)) (PreH11 : (bit_index < 32)) (PreH12 : (un <> 0)) (PreH13 : ((Zabs (un)) <= cap)) (PreH14 : (cap >= 0)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (same_sign z_eq_trunc un )) (PreH17 : (adjust = 0)) (PreH18 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH19 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH20 : (qn > 0)) (PreH21 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH22 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH24 : (list_within_bound UINT_MOD l )) (PreH25 : ((last (l) (1)) >= 1)) (PreH26 : (u__mp_size = un)) (PreH27 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH28 : (u__mp_d = qp)) (PreH29 : (adjust = 0)),
  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z) (ptr: Z),
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) qn ) ”
  &&  “ ((Zabs (qn)) <= cap_2) ”
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs (qn)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs (qn)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_partial_solve_wit_1 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size = 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_2_pure :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (bit_index_pre <= UINT64_MAX)) (PreH2 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (mode_pre <= INT_MAX)) (PreH5 : (cap >= INT_MIN)) (PreH6 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (mode_pre >= INT_MIN)) (PreH9 : (size <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_div_q_2exp_partial_solve_wit_2_pure_split_goal_1 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (bit_index_pre <= UINT64_MAX)) (PreH2 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (mode_pre <= INT_MAX)) (PreH5 : (cap >= INT_MIN)) (PreH6 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (mode_pre >= INT_MIN)) (PreH9 : (size <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_2_aux :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
  &&  “ (size <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_2 := mpz_div_q_2exp_partial_solve_wit_2_pure -> mpz_div_q_2exp_partial_solve_wit_2_aux.

Definition mpz_div_q_2exp_partial_solve_wit_3_pure :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_3_aux :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ”
  &&  “ (mode_pre <> 1) ”
  &&  “ (size > 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (size <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_div_q_2exp_partial_solve_wit_3 := mpz_div_q_2exp_partial_solve_wit_3_pure -> mpz_div_q_2exp_partial_solve_wit_3_aux.

Definition mpz_div_q_2exp_partial_solve_wit_4_pure :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_4_aux :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ”
  &&  “ (mode_pre <> 0) ”
  &&  “ (size <= 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (size <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_div_q_2exp_partial_solve_wit_4 := mpz_div_q_2exp_partial_solve_wit_4_pure -> mpz_div_q_2exp_partial_solve_wit_4_aux.

Definition mpz_div_q_2exp_partial_solve_wit_5_pure :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ”
  &&  “ (limb_cnt >= 0) ”
  &&  “ (1 <= bit_index) ”
  &&  “ (bit_index < 32) ”
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (1 <= (bit_index_pre % ( 32 ) )) ”
  &&  “ ((bit_index_pre ÷ 32 ) >= 0) ”
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index <> 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((bit_index_pre ÷ 32 ) >= 0) ”
  &&  “ (1 <= (bit_index_pre % ( 32 ) )) ”
  &&  “ (1 <= (bit_index_pre % ( 32 ) )) ”
  &&  “ ((bit_index_pre ÷ 32 ) >= 0) ”
).

Definition mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index <> 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((bit_index_pre ÷ 32 ) >= 0) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index <> 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (1 <= (bit_index_pre % ( 32 ) )) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index <> 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (1 <= (bit_index_pre % ( 32 ) )) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index <> 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((bit_index_pre ÷ 32 ) >= 0) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_5_aux :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ”
  &&  “ (limb_cnt >= 0) ”
  &&  “ (1 <= bit_index) ”
  &&  “ (bit_index < 32) ”
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (1 <= (bit_index_pre % ( 32 ) )) ”
  &&  “ ((bit_index_pre ÷ 32 ) >= 0) ”
  &&  “ (bit_index <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ”
  &&  “ (bit_index >= 0) ”
  &&  “ (bit_index < 32) ”
  &&  “ (un <> 0) ”
  &&  “ ((Zabs (un)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  “ (adjust = 0) ”
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ”
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ”
  &&  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = un) ”
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ”
  &&  “ (u__mp_d = qp) ”
  &&  (UIntArray.full qp (qn + limb_cnt ) l )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_5 := mpz_div_q_2exp_partial_solve_wit_5_pure -> mpz_div_q_2exp_partial_solve_wit_5_aux.

Definition mpz_div_q_2exp_partial_solve_wit_6 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((Zlength (l_out)) = qn) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) )) ”
  &&  “ (bit_index <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ”
  &&  “ (bit_index >= 0) ”
  &&  “ (bit_index < 32) ”
  &&  “ (un <> 0) ”
  &&  “ ((Zabs (un)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  “ (adjust = 0) ”
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ”
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ”
  &&  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = un) ”
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ”
  &&  “ (u__mp_d = qp) ”
  &&  (((qp + ((qn - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((qn - 1 ) - 0 ) l_out 0))
  **  (UIntArray.missing_i qp (qn - 1 ) 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_7_pure :=
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn >= 0) ”
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ”
  &&  “ (limb_cnt >= 0) ”
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((bit_index_pre ÷ 32 ) >= 0) ”
) \/
(
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index = 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((bit_index_pre ÷ 32 ) >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) >= 0) ”
).

Definition mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index = 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((bit_index_pre ÷ 32 ) >= 0) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <= UINT64_MAX)) (PreH2 : (u__mp_alloc <= INT_MAX)) (PreH3 : (u__mp_size <= INT_MAX)) (PreH4 : (qn <= INT_MAX)) (PreH5 : (limb_cnt <= INT_MAX)) (PreH6 : (adjust <= INT_MAX)) (PreH7 : (un <= INT_MAX)) (PreH8 : (mode_pre <= INT_MAX)) (PreH9 : (u__mp_alloc >= INT_MIN)) (PreH10 : (u__mp_size >= INT_MIN)) (PreH11 : (qn >= INT_MIN)) (PreH12 : (limb_cnt >= INT_MIN)) (PreH13 : (adjust >= INT_MIN)) (PreH14 : (un >= INT_MIN)) (PreH15 : (mode_pre >= INT_MIN)) (PreH16 : (bit_index = 0)) (PreH17 : (q_pre = u_pre)) (PreH18 : (mode_pre = 2)) (PreH19 : (bit_index_pre >= 0)) (PreH20 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH21 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH22 : (bit_index >= 0)) (PreH23 : (bit_index < 32)) (PreH24 : (un <> 0)) (PreH25 : ((Zabs (un)) <= cap)) (PreH26 : (cap >= 0)) (PreH27 : (cap <= INT_MAX)) (PreH28 : (same_sign z_eq_trunc un )) (PreH29 : (adjust = 0)) (PreH30 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH31 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH32 : (qn > 0)) (PreH33 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH34 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH35 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH36 : (list_within_bound UINT_MOD l )) (PreH37 : ((last (l) (1)) >= 1)) (PreH38 : (u__mp_size = un)) (PreH39 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH40 : (u__mp_d = qp)),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((bit_index_pre ÷ 32 ) >= 0) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_7_aux :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn >= 0) ”
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ”
  &&  “ (limb_cnt >= 0) ”
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((bit_index_pre ÷ 32 ) >= 0) ”
  &&  “ (bit_index = 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ”
  &&  “ (bit_index >= 0) ”
  &&  “ (bit_index < 32) ”
  &&  “ (un <> 0) ”
  &&  “ ((Zabs (un)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  “ (adjust = 0) ”
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ”
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ”
  &&  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = un) ”
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ”
  &&  “ (u__mp_d = qp) ”
  &&  (UIntArray.full qp (qn + limb_cnt ) l )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_7 := mpz_div_q_2exp_partial_solve_wit_7_pure -> mpz_div_q_2exp_partial_solve_wit_7_aux.

Definition mpz_div_q_2exp_partial_solve_wit_8 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0) ”
  &&  “ (mode_pre <> 1) ”
  &&  “ (size > 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (size <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_9 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0) ”
  &&  “ (mode_pre <> 0) ”
  &&  “ (size <= 0) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (size <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_10 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0) ”
  &&  “ ((Zlength (l_out)) = qn) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) )) ”
  &&  “ (bit_index <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ”
  &&  “ (bit_index >= 0) ”
  &&  “ (bit_index < 32) ”
  &&  “ (un <> 0) ”
  &&  “ ((Zabs (un)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  “ (adjust = 0) ”
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ”
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ”
  &&  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = un) ”
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ”
  &&  “ (u__mp_d = qp) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_11 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0) ”
  &&  “ ((Zlength (l_out)) = qn) ”
  &&  “ (list_within_bound UINT_MOD l_out ) ”
  &&  “ (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32))) ”
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) )) ”
  &&  “ (bit_index <> 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ”
  &&  “ (bit_index >= 0) ”
  &&  “ (bit_index < 32) ”
  &&  “ (un <> 0) ”
  &&  “ ((Zabs (un)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  “ (adjust = 0) ”
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ”
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ”
  &&  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = un) ”
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ”
  &&  “ (u__mp_d = qp) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_12 :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)),
  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (bit_index = 0) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (mode_pre = 2) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ”
  &&  “ (bit_index >= 0) ”
  &&  “ (bit_index < 32) ”
  &&  “ (un <> 0) ”
  &&  “ ((Zabs (un)) <= cap) ”
  &&  “ (cap >= 0) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  “ (adjust = 0) ”
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ”
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ”
  &&  “ (qn > 0) ”
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ”
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ ((last (l) (1)) >= 1) ”
  &&  “ (u__mp_size = un) ”
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ”
  &&  “ (u__mp_d = qp) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_13_pure :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (mode_pre: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
|--
  “ (q_pre = q_pre) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_13_aux :=
forall (z_eq_trunc: Z) (q_pre: Z) (u_pre: Z) (bit_index_pre: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )),
  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
|--
  “ (q_pre = q_pre) ”
  &&  “ (q_pre = u_pre) ”
  &&  “ (bit_index_pre >= 0) ”
  &&  “ (un < 0) ”
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
.

Definition mpz_div_q_2exp_partial_solve_wit_13 := mpz_div_q_2exp_partial_solve_wit_13_pure -> mpz_div_q_2exp_partial_solve_wit_13_aux.

(*----- Function mpz_tdiv_q_2exp -----*)

Definition mpz_tdiv_q_2exp_safety_wit_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (cnt_pre: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (cnt_pre >= 0)) (PreH3 : ((cnt_pre ÷ 32 ) <= INT_MAX)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "cnt" ) )) # UInt64  |-> cnt_pre)
  **  (store_Z r_pre z_eq )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpz_tdiv_q_2exp_return_wit_1 :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (cnt_pre: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (r_pre = u_pre)) (PreH3 : (cnt_pre >= 0)) (PreH4 : ((cnt_pre ÷ 32 ) <= INT_MAX)),
  (store_Z r_pre (Z.quot (z_eq) ((Z.pow (2) (cnt_pre)))) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (Z.quot (z_eq) ((Z.pow (2) (cnt_pre)))) )
.

Definition mpz_tdiv_q_2exp_partial_solve_wit_1_pure :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (cnt_pre: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (cnt_pre >= 0)) (PreH3 : ((cnt_pre ÷ 32 ) <= INT_MAX)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "cnt" ) )) # UInt64  |-> cnt_pre)
  **  (store_Z r_pre z_eq )
|--
  “ (r_pre = u_pre) ”
  &&  “ (2 = 2) ”
  &&  “ (cnt_pre >= 0) ”
  &&  “ ((cnt_pre ÷ 32 ) <= INT_MAX) ”
.

Definition mpz_tdiv_q_2exp_partial_solve_wit_1_aux :=
forall (z_eq: Z) (r_pre: Z) (u_pre: Z) (cnt_pre: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (cnt_pre >= 0)) (PreH3 : ((cnt_pre ÷ 32 ) <= INT_MAX)),
  (store_Z r_pre z_eq )
|--
  “ (r_pre = u_pre) ”
  &&  “ (2 = 2) ”
  &&  “ (cnt_pre >= 0) ”
  &&  “ ((cnt_pre ÷ 32 ) <= INT_MAX) ”
  &&  “ (r_pre = u_pre) ”
  &&  “ (cnt_pre >= 0) ”
  &&  “ ((cnt_pre ÷ 32 ) <= INT_MAX) ”
  &&  (store_Z r_pre z_eq )
.

Definition mpz_tdiv_q_2exp_partial_solve_wit_1 := mpz_tdiv_q_2exp_partial_solve_wit_1_pure -> mpz_tdiv_q_2exp_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_div_q_2exp_safety_wit_1 : mpz_div_q_2exp_safety_wit_1.
Axiom proof_of_mpz_div_q_2exp_safety_wit_2 : mpz_div_q_2exp_safety_wit_2.
Axiom proof_of_mpz_div_q_2exp_safety_wit_3 : mpz_div_q_2exp_safety_wit_3.
Axiom proof_of_mpz_div_q_2exp_safety_wit_4 : mpz_div_q_2exp_safety_wit_4.
Axiom proof_of_mpz_div_q_2exp_safety_wit_5 : mpz_div_q_2exp_safety_wit_5.
Axiom proof_of_mpz_div_q_2exp_safety_wit_6 : mpz_div_q_2exp_safety_wit_6.
Axiom proof_of_mpz_div_q_2exp_safety_wit_7 : mpz_div_q_2exp_safety_wit_7.
Axiom proof_of_mpz_div_q_2exp_safety_wit_8 : mpz_div_q_2exp_safety_wit_8.
Axiom proof_of_mpz_div_q_2exp_safety_wit_9 : mpz_div_q_2exp_safety_wit_9.
Axiom proof_of_mpz_div_q_2exp_safety_wit_10 : mpz_div_q_2exp_safety_wit_10.
Axiom proof_of_mpz_div_q_2exp_safety_wit_11 : mpz_div_q_2exp_safety_wit_11.
Axiom proof_of_mpz_div_q_2exp_safety_wit_12 : mpz_div_q_2exp_safety_wit_12.
Axiom proof_of_mpz_div_q_2exp_safety_wit_13 : mpz_div_q_2exp_safety_wit_13.
Axiom proof_of_mpz_div_q_2exp_safety_wit_14 : mpz_div_q_2exp_safety_wit_14.
Axiom proof_of_mpz_div_q_2exp_safety_wit_15 : mpz_div_q_2exp_safety_wit_15.
Axiom proof_of_mpz_div_q_2exp_safety_wit_16 : mpz_div_q_2exp_safety_wit_16.
Axiom proof_of_mpz_div_q_2exp_safety_wit_17 : mpz_div_q_2exp_safety_wit_17.
Axiom proof_of_mpz_div_q_2exp_safety_wit_18 : mpz_div_q_2exp_safety_wit_18.
Axiom proof_of_mpz_div_q_2exp_safety_wit_19 : mpz_div_q_2exp_safety_wit_19.
Axiom proof_of_mpz_div_q_2exp_safety_wit_20 : mpz_div_q_2exp_safety_wit_20.
Axiom proof_of_mpz_div_q_2exp_safety_wit_21 : mpz_div_q_2exp_safety_wit_21.
Axiom proof_of_mpz_div_q_2exp_safety_wit_22 : mpz_div_q_2exp_safety_wit_22.
Axiom proof_of_mpz_div_q_2exp_safety_wit_23 : mpz_div_q_2exp_safety_wit_23.
Axiom proof_of_mpz_div_q_2exp_safety_wit_24 : mpz_div_q_2exp_safety_wit_24.
Axiom proof_of_mpz_div_q_2exp_safety_wit_25 : mpz_div_q_2exp_safety_wit_25.
Axiom proof_of_mpz_div_q_2exp_safety_wit_26 : mpz_div_q_2exp_safety_wit_26.
Axiom proof_of_mpz_div_q_2exp_safety_wit_27 : mpz_div_q_2exp_safety_wit_27.
Axiom proof_of_mpz_div_q_2exp_safety_wit_28 : mpz_div_q_2exp_safety_wit_28.
Axiom proof_of_mpz_div_q_2exp_safety_wit_29 : mpz_div_q_2exp_safety_wit_29.
Axiom proof_of_mpz_div_q_2exp_safety_wit_30 : mpz_div_q_2exp_safety_wit_30.
Axiom proof_of_mpz_div_q_2exp_safety_wit_31 : mpz_div_q_2exp_safety_wit_31.
Axiom proof_of_mpz_div_q_2exp_safety_wit_32 : mpz_div_q_2exp_safety_wit_32.
Axiom proof_of_mpz_div_q_2exp_safety_wit_33 : mpz_div_q_2exp_safety_wit_33.
Axiom proof_of_mpz_div_q_2exp_safety_wit_34 : mpz_div_q_2exp_safety_wit_34.
Axiom proof_of_mpz_div_q_2exp_entail_wit_1 : mpz_div_q_2exp_entail_wit_1.
Axiom proof_of_mpz_div_q_2exp_entail_wit_2_1 : mpz_div_q_2exp_entail_wit_2_1.
Axiom proof_of_mpz_div_q_2exp_entail_wit_2_2 : mpz_div_q_2exp_entail_wit_2_2.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_1 : mpz_div_q_2exp_entail_wit_3_1.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_2 : mpz_div_q_2exp_entail_wit_3_2.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_3 : mpz_div_q_2exp_entail_wit_3_3.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_4 : mpz_div_q_2exp_entail_wit_3_4.
Axiom proof_of_mpz_div_q_2exp_return_wit_1 : mpz_div_q_2exp_return_wit_1.
Axiom proof_of_mpz_div_q_2exp_return_wit_2 : mpz_div_q_2exp_return_wit_2.
Axiom proof_of_mpz_div_q_2exp_return_wit_3 : mpz_div_q_2exp_return_wit_3.
Axiom proof_of_mpz_div_q_2exp_return_wit_4 : mpz_div_q_2exp_return_wit_4.
Axiom proof_of_mpz_div_q_2exp_return_wit_5 : mpz_div_q_2exp_return_wit_5.
Axiom proof_of_mpz_div_q_2exp_return_wit_6 : mpz_div_q_2exp_return_wit_6.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_1 : mpz_div_q_2exp_partial_solve_wit_1.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_2_pure : mpz_div_q_2exp_partial_solve_wit_2_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_2 : mpz_div_q_2exp_partial_solve_wit_2.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_3_pure : mpz_div_q_2exp_partial_solve_wit_3_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_3 : mpz_div_q_2exp_partial_solve_wit_3.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_4_pure : mpz_div_q_2exp_partial_solve_wit_4_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_4 : mpz_div_q_2exp_partial_solve_wit_4.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure : mpz_div_q_2exp_partial_solve_wit_5_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_5 : mpz_div_q_2exp_partial_solve_wit_5.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_6 : mpz_div_q_2exp_partial_solve_wit_6.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure : mpz_div_q_2exp_partial_solve_wit_7_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_7 : mpz_div_q_2exp_partial_solve_wit_7.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_8 : mpz_div_q_2exp_partial_solve_wit_8.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_9 : mpz_div_q_2exp_partial_solve_wit_9.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_10 : mpz_div_q_2exp_partial_solve_wit_10.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_11 : mpz_div_q_2exp_partial_solve_wit_11.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_12 : mpz_div_q_2exp_partial_solve_wit_12.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_13_pure : mpz_div_q_2exp_partial_solve_wit_13_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_13 : mpz_div_q_2exp_partial_solve_wit_13.
Axiom proof_of_mpz_tdiv_q_2exp_safety_wit_1 : mpz_tdiv_q_2exp_safety_wit_1.
Axiom proof_of_mpz_tdiv_q_2exp_return_wit_1 : mpz_tdiv_q_2exp_return_wit_1.
Axiom proof_of_mpz_tdiv_q_2exp_partial_solve_wit_1_pure : mpz_tdiv_q_2exp_partial_solve_wit_1_pure.
Axiom proof_of_mpz_tdiv_q_2exp_partial_solve_wit_1 : mpz_tdiv_q_2exp_partial_solve_wit_1.

End VC_Correct.
