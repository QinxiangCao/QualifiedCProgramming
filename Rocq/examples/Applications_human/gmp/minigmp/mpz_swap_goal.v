From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_swap -----*)

Definition mpz_swap_entail_wit_1_u_read0 :=
(
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (v_pre: Z),
  (store_Z_read0 u_pre n_u_read0 )
  **  (store_Z v_pre m_u_read0 )
|--
  EX (vptr: Z) (uptr: Z) (vcap: Z) (vsize: Z) (ucap: Z) (usize: Z),
  “ ((Zabs (usize)) <= ucap) ”
  &&  “ (same_sign n_u_read0 usize ) ”
  &&  “ ((Zabs (vsize)) <= vcap) ”
  &&  “ (same_sign m_u_read0 vsize ) ”
  &&  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
) \/
(
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign m_u_read0 size )) (PreH2 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m_u_read0)) (Zabs (size)) )
  **  (store_Z_read0 u_pre n_u_read0 )
|--
  EX (uptr: Z) (ucap: Z) (usize: Z),
  “ ((Zabs (usize)) <= ucap) ”
  &&  “ (same_sign n_u_read0 usize ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (same_sign m_u_read0 size ) ”
  &&  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m_u_read0)) (Zabs (size)) )
).

Definition mpz_swap_entail_wit_2_u_read0 :=
(
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (v_pre: Z) (uptr: Z) (usize: Z) (ucap: Z) (vptr: Z) (vsize: Z) (vcap: Z) (PreH1 : ((Zabs (usize)) <= ucap)) (PreH2 : (same_sign n_u_read0 usize )) (PreH3 : ((Zabs (vsize)) <= vcap)) (PreH4 : (same_sign m_u_read0 vsize )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
|--
  (store_Z u_pre m_u_read0 )
  **  (store_Z_read0 v_pre n_u_read0 )
) \/
(
forall (m_u_read0: Z) (n_u_read0: Z) (v_pre: Z) (uptr: Z) (usize: Z) (ucap: Z) (vptr: Z) (vsize: Z) (vcap: Z) (PreH1 : (ucap <= INT_MAX)) (PreH2 : (usize <= INT_MAX)) (PreH3 : (ucap >= INT_MIN)) (PreH4 : (usize >= INT_MIN)) (PreH5 : ((Zabs (usize)) <= ucap)) (PreH6 : (same_sign n_u_read0 usize )) (PreH7 : ((Zabs (vsize)) <= vcap)) (PreH8 : (same_sign m_u_read0 vsize )),
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
|--
  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (store_Z_read0 v_pre n_u_read0 )
).

Definition mpz_swap_entail_wit_2_u_read0_split_goal_spatial :=
forall (m_u_read0: Z) (n_u_read0: Z) (v_pre: Z) (uptr: Z) (usize: Z) (ucap: Z) (vptr: Z) (vsize: Z) (vcap: Z) (PreH1 : (ucap <= INT_MAX)) (PreH2 : (usize <= INT_MAX)) (PreH3 : (ucap >= INT_MIN)) (PreH4 : (usize >= INT_MIN)) (PreH5 : ((Zabs (usize)) <= ucap)) (PreH6 : (same_sign n_u_read0 usize )) (PreH7 : ((Zabs (vsize)) <= vcap)) (PreH8 : (same_sign m_u_read0 vsize )),
  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
|--
  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (store_Z_read0 v_pre n_u_read0 )
.

Definition mpz_swap_return_wit_1_plain :=
forall (m_plain: Z) (n_plain: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m_plain size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n_plain size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_plain)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_plain)) (Zabs (size)) )
|--
  (store_Z u_pre m_plain )
  **  (store_Z v_pre n_plain )
.

Definition mpz_swap_return_wit_2_u_read0 :=
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (v_pre: Z),
  (store_Z u_pre m_u_read0 )
  **  (store_Z_read0 v_pre n_u_read0 )
|--
  (store_Z u_pre m_u_read0 )
  **  (store_Z_read0 v_pre n_u_read0 )
.

Definition mpz_swap_partial_solve_wit_1_plain :=
forall (m_plain: Z) (n_plain: Z) (u_pre: Z) (v_pre: Z),
  (store_Z u_pre n_plain )
  **  (store_Z v_pre m_plain )
|--
  EX (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign m_plain size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_plain size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_plain)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_plain)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_swap_partial_solve_wit_2_u_read0 :=
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (v_pre: Z) (uptr: Z) (usize: Z) (ucap: Z) (vptr: Z) (vsize: Z) (vcap: Z) (PreH1 : ((Zabs (usize)) <= ucap)) (PreH2 : (same_sign n_u_read0 usize )) (PreH3 : ((Zabs (vsize)) <= vcap)) (PreH4 : (same_sign m_u_read0 vsize )),
  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
|--
  “ ((Zabs (usize)) <= ucap) ”
  &&  “ (same_sign n_u_read0 usize ) ”
  &&  “ ((Zabs (vsize)) <= vcap) ”
  &&  “ (same_sign m_u_read0 vsize ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
.

Definition mpz_swap_partial_solve_wit_3_plain :=
forall (m_plain: Z) (n_plain: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m_plain size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n_plain size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_plain)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_plain)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign m_plain size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_plain size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_plain)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_plain)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_swap_partial_solve_wit_4_u_read0 :=
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (v_pre: Z) (uptr: Z) (usize: Z) (ucap: Z) (vptr: Z) (vsize: Z) (vcap: Z) (PreH1 : ((Zabs (usize)) <= ucap)) (PreH2 : (same_sign n_u_read0 usize )) (PreH3 : ((Zabs (vsize)) <= vcap)) (PreH4 : (same_sign m_u_read0 vsize )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
|--
  “ ((Zabs (usize)) <= ucap) ”
  &&  “ (same_sign n_u_read0 usize ) ”
  &&  “ ((Zabs (vsize)) <= vcap) ”
  &&  “ (same_sign m_u_read0 vsize ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
.

Definition mpz_swap_partial_solve_wit_5_plain :=
forall (m_plain: Z) (n_plain: Z) (u_pre: Z) (v_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m_plain size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n_plain size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_plain)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_plain)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign m_plain size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (same_sign n_plain size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_plain)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_plain)) (Zabs (size)) )
.

Definition mpz_swap_partial_solve_wit_6_u_read0 :=
forall (m_u_read0: Z) (n_u_read0: Z) (u_pre: Z) (v_pre: Z) (uptr: Z) (usize: Z) (ucap: Z) (vptr: Z) (vsize: Z) (vcap: Z) (PreH1 : ((Zabs (usize)) <= ucap)) (PreH2 : (same_sign n_u_read0 usize )) (PreH3 : ((Zabs (vsize)) <= vcap)) (PreH4 : (same_sign m_u_read0 vsize )),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
|--
  “ ((Zabs (usize)) <= ucap) ”
  &&  “ (same_sign n_u_read0 usize ) ”
  &&  “ ((Zabs (vsize)) <= vcap) ”
  &&  “ (same_sign m_u_read0 vsize ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> usize)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> vsize)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> vptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> uptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> vcap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ucap)
  **  (mpd_store_Z_compact_read0 uptr (Zabs (n_u_read0)) (Zabs (usize)) )
  **  (UIntArray.undef_seg uptr (Zmax ((Zabs (usize))) (1)) ucap )
  **  (mpd_store_Z_compact UINT_MOD vptr (Zabs (m_u_read0)) (Zabs (vsize)) )
  **  (UIntArray.undef_seg vptr (Zabs (vsize)) vcap )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_swap_entail_wit_1_u_read0 : mpz_swap_entail_wit_1_u_read0.
Axiom proof_of_mpz_swap_entail_wit_2_u_read0 : mpz_swap_entail_wit_2_u_read0.
Axiom proof_of_mpz_swap_return_wit_1_plain : mpz_swap_return_wit_1_plain.
Axiom proof_of_mpz_swap_return_wit_2_u_read0 : mpz_swap_return_wit_2_u_read0.
Axiom proof_of_mpz_swap_partial_solve_wit_1_plain : mpz_swap_partial_solve_wit_1_plain.
Axiom proof_of_mpz_swap_partial_solve_wit_2_u_read0 : mpz_swap_partial_solve_wit_2_u_read0.
Axiom proof_of_mpz_swap_partial_solve_wit_3_plain : mpz_swap_partial_solve_wit_3_plain.
Axiom proof_of_mpz_swap_partial_solve_wit_4_u_read0 : mpz_swap_partial_solve_wit_4_u_read0.
Axiom proof_of_mpz_swap_partial_solve_wit_5_plain : mpz_swap_partial_solve_wit_5_plain.
Axiom proof_of_mpz_swap_partial_solve_wit_6_u_read0 : mpz_swap_partial_solve_wit_6_u_read0.

End VC_Correct.
