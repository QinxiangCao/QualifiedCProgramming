From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mrz_realloc_if -----*)

Definition mrz_realloc_if_return_wit_1_preserving :=
(
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  EX (z__mp_alloc: Z),
  “ (same_sign m_preserving old_preserving ) ”
  &&  “ (z__mp_alloc = (Z.max (n_pre) (cap_preserving))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) (Z.max (n_pre) (cap_preserving)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
) \/
(
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  “ (cap_preserving = (Z.max (n_pre) (cap_preserving))) ”
  &&  “ (cap_preserving = (Z.max (n_pre) (cap_preserving))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) (Z.max (n_pre) (cap_preserving)) )
).

Definition mrz_realloc_if_return_wit_1_preserving_split_goal_1 :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  “ (cap_preserving = (Z.max (n_pre) (cap_preserving))) ”
.

Definition mrz_realloc_if_return_wit_1_preserving_split_goal_2 :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  “ (cap_preserving = (Z.max (n_pre) (cap_preserving))) ”
.

Definition mrz_realloc_if_return_wit_1_preserving_split_goal_spatial :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) (Z.max (n_pre) (cap_preserving)) )
.

Definition mrz_realloc_if_return_wit_2_raw :=
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  EX (z__mp_alloc: Z),
  “ (z__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full ptr_raw (Z.max (n_pre) (cap_raw)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
  &&  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full ptr_raw (Z.max (n_pre) (cap_raw)) )
).

Definition mrz_realloc_if_return_wit_2_raw_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_2_raw_split_goal_2 :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_2_raw_split_goal_spatial :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (n_pre: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  (UIntArray.undef_full ptr_raw (Z.max (n_pre) (cap_raw)) )
.

Definition mrz_realloc_if_return_wit_3_raw :=
(
forall (cap_raw: Z) (sz_raw: Z) (z_pre: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (z__mp_alloc: Z),
  “ (z__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full retval (Z.max (n_pre) (cap_raw)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  “ (r__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  “ (r__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full retval (Z.max (n_pre) (cap_raw)) )
).

Definition mrz_realloc_if_return_wit_3_raw_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  “ (r__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_3_raw_split_goal_2 :=
forall (cap_raw: Z) (sz_raw: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  “ (r__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_3_raw_split_goal_spatial :=
forall (cap_raw: Z) (sz_raw: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  (UIntArray.undef_full retval (Z.max (n_pre) (cap_raw)) )
.

Definition mrz_realloc_if_return_wit_4_preserving :=
(
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (z_pre: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m_preserving old_preserving )) (PreH2 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap_preserving)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (1)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (z__mp_alloc: Z),
  “ (same_sign m_preserving old_preserving ) ”
  &&  “ (z__mp_alloc = (Z.max (n_pre) (cap_preserving))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (cap_preserving)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m_preserving old_preserving )) (PreH2 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap_preserving)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (1)) )
|--
  “ (r__mp_alloc = (Z.max (n_pre) (cap_preserving))) ”
  &&  “ (r__mp_alloc = (Z.max (n_pre) (cap_preserving))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (cap_preserving)) )
).

Definition mrz_realloc_if_return_wit_4_preserving_split_goal_1 :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m_preserving old_preserving )) (PreH2 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap_preserving)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (1)) )
|--
  “ (r__mp_alloc = (Z.max (n_pre) (cap_preserving))) ”
.

Definition mrz_realloc_if_return_wit_4_preserving_split_goal_2 :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m_preserving old_preserving )) (PreH2 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap_preserving)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (1)) )
|--
  “ (r__mp_alloc = (Z.max (n_pre) (cap_preserving))) ”
.

Definition mrz_realloc_if_return_wit_4_preserving_split_goal_spatial :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (n_pre: Z) (r__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m_preserving old_preserving )) (PreH2 : (r__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap_preserving)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (1)) )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (n_pre) (cap_preserving)) )
.

Definition mrz_realloc_if_partial_solve_wit_1_raw_pure :=
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (n_pre > cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (n_pre >= cap_raw) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (1))) ”
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (cap_raw >= INT_MIN)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre > cap_raw)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (1))) ”
).

Definition mrz_realloc_if_partial_solve_wit_1_raw_pure_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (cap_raw >= INT_MIN)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre > cap_raw)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (1))) ”
.

Definition mrz_realloc_if_partial_solve_wit_1_raw_aux :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (n_pre > cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))),
  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (n_pre >= cap_raw) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (1))) ”
  &&  “ (n_pre > cap_raw) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
.

Definition mrz_realloc_if_partial_solve_wit_1_raw := mrz_realloc_if_partial_solve_wit_1_raw_pure -> mrz_realloc_if_partial_solve_wit_1_raw_aux.

Definition mrz_realloc_if_partial_solve_wit_2_preserving_pure :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (n_pre > cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (n_pre >= cap_preserving) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign m_preserving old_preserving ) ”
.

Definition mrz_realloc_if_partial_solve_wit_2_preserving_aux :=
forall (m_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (z_pre: Z) (n_pre: Z) (PreH1 : (n_pre > cap_preserving)) (PreH2 : (cap_preserving >= 0)) (PreH3 : (cap_preserving <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign m_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (n_pre >= cap_preserving) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign m_preserving old_preserving ) ”
  &&  “ (n_pre > cap_preserving) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign m_preserving old_preserving ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (m_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
.

Definition mrz_realloc_if_partial_solve_wit_2_preserving := mrz_realloc_if_partial_solve_wit_2_preserving_pure -> mrz_realloc_if_partial_solve_wit_2_preserving_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mrz_realloc_if_return_wit_1_preserving : mrz_realloc_if_return_wit_1_preserving.
Axiom proof_of_mrz_realloc_if_return_wit_2_raw : mrz_realloc_if_return_wit_2_raw.
Axiom proof_of_mrz_realloc_if_return_wit_3_raw : mrz_realloc_if_return_wit_3_raw.
Axiom proof_of_mrz_realloc_if_return_wit_4_preserving : mrz_realloc_if_return_wit_4_preserving.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1_raw_pure : mrz_realloc_if_partial_solve_wit_1_raw_pure.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1_raw : mrz_realloc_if_partial_solve_wit_1_raw.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_2_preserving_pure : mrz_realloc_if_partial_solve_wit_2_preserving_pure.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_2_preserving : mrz_realloc_if_partial_solve_wit_2_preserving.

End VC_Correct.
