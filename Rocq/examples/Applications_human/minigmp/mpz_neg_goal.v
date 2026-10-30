From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Require Import SimpleC.EE.Applications_human.minigmp.mpz_neg_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_strategy_proof.

(*----- Function mpz_neg -----*)

Definition mpz_neg_safety_wit_1 :=
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
  **  ((( &( "digits" ) )) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (size <> (INT_MIN)) ”
) \/
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
  **  ((( &( "digits" ) )) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (size <> (INT_MIN)) ”
).

Definition mpz_neg_safety_wit_1_split_goal_1 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
  **  ((( &( "digits" ) )) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (size <> (INT_MIN)) ”
.

Definition mpz_neg_return_wit_1 :=
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-size))
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (store_Z u_pre (-m) )
  **  (store_Z v_pre m )
) \/
(
forall (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
|--
  “ ((Zabs ((-size))) <= retval) ”
  &&  “ (same_sign (-m) (-size) ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs ((-size))) retval )
  **  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs ((-m))) (Zabs ((-size))) )
).

Definition mpz_neg_return_wit_1_split_goal_1 :=
forall (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
|--
  “ ((Zabs ((-size))) <= retval) ”
.

Definition mpz_neg_return_wit_1_split_goal_2 :=
forall (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
|--
  “ (same_sign (-m) (-size) ) ”
.

Definition mpz_neg_return_wit_1_split_goal_spatial :=
forall (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) )) (PreH2 : (same_sign n size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (mpd_store_Z UINT_MOD retval_2 (Zabs (m)) retval )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs ((-size))) retval )
  **  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs ((-m))) (Zabs ((-size))) )
.

Definition mpz_neg_partial_solve_wit_1 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z),
  (store_Z u_pre n )
  **  (store_Z v_pre m )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign m size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z u_pre n )
.

Definition mpz_neg_partial_solve_wit_2_pure :=
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign m size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((( &( "count" ) )) # Int  |->_)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (store_Z u_pre n )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
) \/
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((( &( "count" ) )) # Int  |->_)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (store_Z u_pre n )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_neg_partial_solve_wit_2_pure_split_goal_1 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign m size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((( &( "count" ) )) # Int  |->_)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (store_Z u_pre n )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_neg_partial_solve_wit_2_aux :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign m size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z u_pre n )
|--
  “ (size <= INT_MAX) ”
  &&  “ (INT_MIN < size) ”
  &&  “ (same_sign m size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z u_pre n )
.

Definition mpz_neg_partial_solve_wit_2 := mpz_neg_partial_solve_wit_2_pure -> mpz_neg_partial_solve_wit_2_aux.

Definition mpz_neg_partial_solve_wit_3 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (same_sign m size )) (PreH3 : ((Zabs (size)) <= cap)),
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z u_pre n )
|--
  EX (ptr_2: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign n size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (same_sign m size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_neg_partial_solve_wit_4 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign m size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (same_sign n size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (same_sign m size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_neg_partial_solve_wit_5_pure :=
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign m size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((( &( "digits" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (retval >= 0) ”
) \/
(
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (size_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (cap >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (size_2 >= INT_MIN)) (PreH10 : (cap_2 >= INT_MIN)) (PreH11 : (same_sign n size_2 )) (PreH12 : ((Zabs (size_2)) <= cap_2)) (PreH13 : (retval = (Zabs (size)))) (PreH14 : (same_sign m size )) (PreH15 : ((Zabs (size)) <= cap)),
  ((( &( "digits" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (retval >= 0) ”
).

Definition mpz_neg_partial_solve_wit_5_pure_split_goal_1 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (size_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (cap >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (size_2 >= INT_MIN)) (PreH10 : (cap_2 >= INT_MIN)) (PreH11 : (same_sign n size_2 )) (PreH12 : ((Zabs (size_2)) <= cap_2)) (PreH13 : (retval = (Zabs (size)))) (PreH14 : (same_sign m size )) (PreH15 : ((Zabs (size)) <= cap)),
  ((( &( "digits" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (retval >= 0) ”
.

Definition mpz_neg_partial_solve_wit_5_aux :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign m size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (retval >= 0) ”
  &&  “ (same_sign n size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (same_sign m size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_neg_partial_solve_wit_5 := mpz_neg_partial_solve_wit_5_pure -> mpz_neg_partial_solve_wit_5_aux.

Definition mpz_neg_partial_solve_wit_6 :=
forall (m: Z) (n: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (same_sign m size )) (PreH5 : ((Zabs (size)) <= cap)),
  (UIntArray.undef_full retval_2 retval )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (size)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (is_compact_Z UINT_MOD (Zabs (m)) (Zabs (size)) ) ”
  &&  “ (same_sign n size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (retval = (Zabs (size))) ”
  &&  “ (same_sign m size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z UINT_MOD ptr (Zabs (m)) retval )
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

(* Shallow FunAssertion specs for mpz_neg. *)
Definition mpz_neg_sig : FuncSig := ([ * struct "__mpz_struct";  * struct "__mpz_struct"], void)%ctype.

Definition mpz_neg_default : Spec mpz_neg_sig :=
  fun F =>
ALL (n: Z),
ALL (m: Z),
HoareFun ([ * struct "__mpz_struct";  * struct "__mpz_struct"], void)%ctype
  (fun '(u_pre, v_pre) =>
  ((store_Z u_pre n )
  **  (store_Z v_pre m )))
  (fun '(u_pre, v_pre) (_retval : unit) =>
  ((store_Z u_pre (-m) )
  **  (store_Z v_pre m )))
  F.

Definition mpz_neg_exported : Spec mpz_neg_sig :=
  fun F =>
ALL (n: Z),
ALL (m: Z),
HoareFun ([ * struct "__mpz_struct";  * struct "__mpz_struct"], void)%ctype
  (fun '(u_pre, v_pre) =>
  ((store_Z u_pre n )
  **  (store_Z v_pre m )))
  (fun '(u_pre, v_pre) (_retval : unit) =>
  ((store_Z u_pre (-m) )
  **  (store_Z v_pre m )))
  F.

Definition mpz_neg_default_entail_exported :=
forall (u_pre: Z) (v_pre: Z) (n_exported: Z) (m_exported: Z),
  ((store_Z u_pre n_exported )
  **  (store_Z v_pre m_exported ))
|--
EX (n: Z)(m: Z),
  ((store_Z u_pre n )
  **  (store_Z v_pre m ))
  **
  (  ((store_Z u_pre (-m) )
  **  (store_Z v_pre m ))
  -*
  ((store_Z u_pre (-m_exported) )
  **  (store_Z v_pre m_exported )))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.

Axiom proof_of_mpz_neg_safety_wit_1 : mpz_neg_safety_wit_1.
Axiom proof_of_mpz_neg_return_wit_1 : mpz_neg_return_wit_1.
Axiom proof_of_mpz_neg_partial_solve_wit_1 : mpz_neg_partial_solve_wit_1.
Axiom proof_of_mpz_neg_partial_solve_wit_2_pure : mpz_neg_partial_solve_wit_2_pure.
Axiom proof_of_mpz_neg_partial_solve_wit_2 : mpz_neg_partial_solve_wit_2.
Axiom proof_of_mpz_neg_partial_solve_wit_3 : mpz_neg_partial_solve_wit_3.
Axiom proof_of_mpz_neg_partial_solve_wit_4 : mpz_neg_partial_solve_wit_4.
Axiom proof_of_mpz_neg_partial_solve_wit_5_pure : mpz_neg_partial_solve_wit_5_pure.
Axiom proof_of_mpz_neg_partial_solve_wit_5 : mpz_neg_partial_solve_wit_5.
Axiom proof_of_mpz_neg_partial_solve_wit_6 : mpz_neg_partial_solve_wit_6.
Axiom proof_of_mpz_neg_default_entail_exported : mpz_neg_default_entail_exported.

End VC_Correct.
