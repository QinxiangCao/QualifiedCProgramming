From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_realloc -----*)

Definition mpz_realloc_safety_wit_1_preserving :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (PreH1 : (size_pre >= cap_preserving)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap_preserving >= 0)) (PreH4 : (cap_preserving <= INT_MAX)) (PreH5 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH6 : (same_sign n_preserving old_preserving )),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_realloc_safety_wit_2_raw :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (PreH1 : (size_pre >= cap_raw)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_realloc_safety_wit_3_raw :=
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)),
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ False ”
.

Definition mpz_realloc_safety_wit_4_raw :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ False ”
.

Definition mpz_realloc_safety_wit_5_preserving :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old_preserving)) retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_realloc_safety_wit_6_preserving :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_realloc_return_wit_1_preserving :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r__mp_alloc: Z),
  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (r__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_1_preserving_split_goal_spatial :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_2_raw :=
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r__mp_alloc: Z),
  “ (r__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (UIntArray.undef_full ptr_raw cap_raw )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_2_raw_split_goal_spatial :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (UIntArray.undef_full ptr_raw cap_raw )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_3_preserving :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r__mp_alloc: Z),
  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (r__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mpz_realloc_return_wit_4_raw :=
(
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (UIntArray.undef_full retval retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  EX (r__mp_alloc: Z),
  “ (r__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)),
  (UIntArray.undef_full retval retval_2 )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_4_raw_split_goal_spatial :=
forall (cap_raw: Z) (sz_raw: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)),
  (UIntArray.undef_full retval retval_2 )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_5_preserving :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r__mp_alloc: Z),
  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (r__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  “ (0 = old_preserving) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_5_preserving_split_goal_1 :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  “ (0 = old_preserving) ”
.

Definition mpz_realloc_return_wit_5_preserving_split_goal_spatial :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving = 0)),
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_6_preserving :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r__mp_alloc: Z),
  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (r__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval (Zabs (old_preserving)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (size_pre: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving <> 0)),
  TT && emp 
|--
  “ (0 = old_preserving) ”
  &&  emp
).

Definition mpz_realloc_return_wit_6_preserving_split_goal_1 :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (size_pre: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old_preserving)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_preserving)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_preserving >= 0)) (PreH7 : (cap_preserving <= INT_MAX)) (PreH8 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH9 : (same_sign n_preserving old_preserving )) (PreH10 : (cap_preserving <> 0)),
  (0 = old_preserving)
.

Definition mpz_realloc_partial_solve_wit_1_preserving :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (PreH1 : (size_pre >= cap_preserving)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap_preserving >= 0)) (PreH4 : (cap_preserving <= INT_MAX)) (PreH5 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH6 : (same_sign n_preserving old_preserving )),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (size_pre >= cap_preserving) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign n_preserving old_preserving ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
.

Definition mpz_realloc_partial_solve_wit_2_raw :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (PreH1 : (size_pre >= cap_raw)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))),
  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
.

Definition mpz_realloc_partial_solve_wit_3_raw :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)),
  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  “ (cap_raw <> 0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
.

Definition mpz_realloc_partial_solve_wit_4_raw_pure :=
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
  **  (mpd_store_Z_compact UINT_MOD ptr_raw 0 0 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  (UIntArray.undef_seg ptr_raw 0 cap_raw )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (cap_raw >= 0) ”
  &&  “ (retval >= cap_raw) ”
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cap_raw >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
  **  (mpd_store_Z_compact UINT_MOD ptr_raw 0 0 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  (UIntArray.undef_seg ptr_raw 0 cap_raw )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (retval >= cap_raw) ”
).

Definition mpz_realloc_partial_solve_wit_4_raw_pure_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cap_raw >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
  **  (mpd_store_Z_compact UINT_MOD ptr_raw 0 0 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  (UIntArray.undef_seg ptr_raw 0 cap_raw )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (retval >= cap_raw) ”
.

Definition mpz_realloc_partial_solve_wit_4_raw_aux :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
  **  (mpd_store_Z_compact UINT_MOD ptr_raw 0 0 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  (UIntArray.undef_seg ptr_raw 0 cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (cap_raw >= 0) ”
  &&  “ (retval >= cap_raw) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  “ (cap_raw <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_raw 0 0 )
  **  (UIntArray.undef_seg ptr_raw 0 cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
.

Definition mpz_realloc_partial_solve_wit_4_raw := mpz_realloc_partial_solve_wit_4_raw_pure -> mpz_realloc_partial_solve_wit_4_raw_aux.

Definition mpz_realloc_partial_solve_wit_5_preserving_pure :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (cap_preserving >= 0) ”
  &&  “ (retval >= cap_preserving) ”
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_preserving >= INT_MIN)) (PreH4 : (old_preserving >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_preserving)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_preserving >= 0)) (PreH10 : (cap_preserving <= INT_MAX)) (PreH11 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH12 : (same_sign n_preserving old_preserving )) (PreH13 : (cap_preserving <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (retval >= cap_preserving) ”
).

Definition mpz_realloc_partial_solve_wit_5_preserving_pure_split_goal_1 :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_preserving >= INT_MIN)) (PreH4 : (old_preserving >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_preserving)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_preserving >= 0)) (PreH10 : (cap_preserving <= INT_MAX)) (PreH11 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH12 : (same_sign n_preserving old_preserving )) (PreH13 : (cap_preserving <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (retval >= cap_preserving) ”
.

Definition mpz_realloc_partial_solve_wit_5_preserving_aux :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (cap_preserving >= 0) ”
  &&  “ (retval >= cap_preserving) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_preserving) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (cap_preserving <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
.

Definition mpz_realloc_partial_solve_wit_5_preserving := mpz_realloc_partial_solve_wit_5_preserving_pure -> mpz_realloc_partial_solve_wit_5_preserving_aux.

Definition mpz_realloc_partial_solve_wit_6_raw :=
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)),
  (mpd_store_Z_compact UINT_MOD retval_2 0 0 )
  **  (UIntArray.undef_seg retval_2 0 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  “ (cap_raw <> 0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (mpd_store_Z_compact UINT_MOD retval_2 0 0 )
  **  (UIntArray.undef_seg retval_2 0 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
.

Definition mpz_realloc_partial_solve_wit_7_raw_pure :=
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval >= 0) ”
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_raw >= INT_MIN)) (PreH4 : (sz_raw >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw = 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval >= 0) ”
).

Definition mpz_realloc_partial_solve_wit_7_raw_pure_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_raw >= INT_MIN)) (PreH4 : (sz_raw >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw = 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval >= 0) ”
.

Definition mpz_realloc_partial_solve_wit_7_raw_aux :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)),
  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval >= 0) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  “ (cap_raw = 0) ”
  &&  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
.

Definition mpz_realloc_partial_solve_wit_7_raw := mpz_realloc_partial_solve_wit_7_raw_pure -> mpz_realloc_partial_solve_wit_7_raw_aux.

Definition mpz_realloc_partial_solve_wit_8_preserving_pure :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving = 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (retval >= 0) ”
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_preserving >= INT_MIN)) (PreH4 : (old_preserving >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_preserving)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_preserving >= 0)) (PreH10 : (cap_preserving <= INT_MAX)) (PreH11 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH12 : (same_sign n_preserving old_preserving )) (PreH13 : (cap_preserving = 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (retval >= 0) ”
).

Definition mpz_realloc_partial_solve_wit_8_preserving_pure_split_goal_1 :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_preserving >= INT_MIN)) (PreH4 : (old_preserving >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_preserving)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_preserving >= 0)) (PreH10 : (cap_preserving <= INT_MAX)) (PreH11 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH12 : (same_sign n_preserving old_preserving )) (PreH13 : (cap_preserving = 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (retval >= 0) ”
.

Definition mpz_realloc_partial_solve_wit_8_preserving_aux :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving = 0)),
  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
|--
  “ (retval >= 0) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_preserving) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (cap_preserving = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_preserving)
.

Definition mpz_realloc_partial_solve_wit_8_preserving := mpz_realloc_partial_solve_wit_8_preserving_pure -> mpz_realloc_partial_solve_wit_8_preserving_aux.

Definition mpz_realloc_partial_solve_wit_9_raw_pure :=
(
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)),
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (sz_raw <= INT_MAX) ”
  &&  “ (INT_MIN < sz_raw) ”
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw <> 0)),
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (INT_MIN < sz_raw) ”
).

Definition mpz_realloc_partial_solve_wit_9_raw_pure_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw <> 0)),
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (INT_MIN < sz_raw) ”
.

Definition mpz_realloc_partial_solve_wit_9_raw_aux :=
forall (cap_raw: Z) (sz_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (sz_raw <= INT_MAX) ”
  &&  “ (INT_MIN < sz_raw) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  “ (cap_raw <> 0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
.

Definition mpz_realloc_partial_solve_wit_9_raw := mpz_realloc_partial_solve_wit_9_raw_pure -> mpz_realloc_partial_solve_wit_9_raw_aux.

Definition mpz_realloc_partial_solve_wit_10_preserving_pure :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old_preserving)) retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old_preserving <= INT_MAX) ”
  &&  “ (INT_MIN < old_preserving) ”
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old_preserving >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_preserving)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_preserving >= 0)) (PreH9 : (cap_preserving <= INT_MAX)) (PreH10 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH11 : (same_sign n_preserving old_preserving )) (PreH12 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old_preserving)) retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old_preserving) ”
).

Definition mpz_realloc_partial_solve_wit_10_preserving_pure_split_goal_1 :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old_preserving >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_preserving)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_preserving >= 0)) (PreH9 : (cap_preserving <= INT_MAX)) (PreH10 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH11 : (same_sign n_preserving old_preserving )) (PreH12 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old_preserving)) retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old_preserving) ”
.

Definition mpz_realloc_partial_solve_wit_10_preserving_aux :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving <> 0)),
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old_preserving)) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old_preserving <= INT_MAX) ”
  &&  “ (INT_MIN < old_preserving) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_preserving) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (cap_preserving <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old_preserving)) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_10_preserving := mpz_realloc_partial_solve_wit_10_preserving_pure -> mpz_realloc_partial_solve_wit_10_preserving_aux.

Definition mpz_realloc_partial_solve_wit_11_raw_pure :=
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (sz_raw <= INT_MAX) ”
  &&  “ (INT_MIN < sz_raw) ”
) \/
(
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < sz_raw) ”
).

Definition mpz_realloc_partial_solve_wit_11_raw_pure_split_goal_1 :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < sz_raw) ”
.

Definition mpz_realloc_partial_solve_wit_11_raw_aux :=
forall (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (sz_raw <= INT_MAX) ”
  &&  “ (INT_MIN < sz_raw) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_raw) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_raw >= 0) ”
  &&  “ (cap_raw <= INT_MAX) ”
  &&  “ ((Zabs (sz_raw)) <= (Z.max (size_pre) (1))) ”
  &&  “ (cap_raw = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_11_raw := mpz_realloc_partial_solve_wit_11_raw_pure -> mpz_realloc_partial_solve_wit_11_raw_aux.

Definition mpz_realloc_partial_solve_wit_12_preserving_pure :=
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old_preserving <= INT_MAX) ”
  &&  “ (INT_MIN < old_preserving) ”
) \/
(
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old_preserving >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_preserving)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_preserving >= 0)) (PreH9 : (cap_preserving <= INT_MAX)) (PreH10 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH11 : (same_sign n_preserving old_preserving )) (PreH12 : (cap_preserving = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old_preserving) ”
).

Definition mpz_realloc_partial_solve_wit_12_preserving_pure_split_goal_1 :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (old_preserving <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old_preserving >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_preserving)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_preserving >= 0)) (PreH9 : (cap_preserving <= INT_MAX)) (PreH10 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH11 : (same_sign n_preserving old_preserving )) (PreH12 : (cap_preserving = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old_preserving) ”
.

Definition mpz_realloc_partial_solve_wit_12_preserving_aux :=
forall (n_preserving: Z) (cap_preserving: Z) (old_preserving: Z) (ptr_preserving: Z) (r_pre: Z) (size_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_preserving)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_preserving >= 0)) (PreH5 : (cap_preserving <= INT_MAX)) (PreH6 : ((Zabs (old_preserving)) <= cap_preserving)) (PreH7 : (same_sign n_preserving old_preserving )) (PreH8 : (cap_preserving = 0)),
  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old_preserving <= INT_MAX) ”
  &&  “ (INT_MIN < old_preserving) ”
  &&  “ (retval = (Z.max (size_pre) (1))) ”
  &&  “ (size_pre >= cap_preserving) ”
  &&  “ (size_pre <= INT_MAX) ”
  &&  “ (cap_preserving >= 0) ”
  &&  “ (cap_preserving <= INT_MAX) ”
  &&  “ ((Zabs (old_preserving)) <= cap_preserving) ”
  &&  “ (same_sign n_preserving old_preserving ) ”
  &&  “ (cap_preserving = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_preserving (Zabs (n_preserving)) (Zabs (old_preserving)) )
  **  (UIntArray.undef_seg ptr_preserving (Zabs (old_preserving)) cap_preserving )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old_preserving)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_12_preserving := mpz_realloc_partial_solve_wit_12_preserving_pure -> mpz_realloc_partial_solve_wit_12_preserving_aux.

Definition mpz_realloc_which_implies_wit_1 :=
(
forall (r: Z) (r__mp_alloc: Z) (r__mp_d: Z),
  ((&((r)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_full r__mp_d r__mp_alloc )
|--
  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  (UIntArray.undef_seg r__mp_d 0 r__mp_alloc )
) \/
(
forall (r__mp_d: Z),
  TT && emp 
|--
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
).

Definition mpz_realloc_which_implies_wit_1_split_goal_spatial :=
forall (r__mp_d: Z),
  TT && emp 
|--
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
.

Definition mpz_realloc_which_implies_wit_2 :=
(
forall (r: Z) (r__mp_d: Z) (size: Z),
  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  (UIntArray.undef_seg r__mp_d 0 size )
|--
  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_full r__mp_d size )
) \/
(
forall (r__mp_d: Z) (size: Z),
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  (UIntArray.undef_seg r__mp_d 0 size )
|--
  (UIntArray.undef_full r__mp_d size )
).

Definition mpz_realloc_which_implies_wit_2_split_goal_spatial :=
forall (r__mp_d: Z) (size: Z),
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  (UIntArray.undef_seg r__mp_d 0 size )
|--
  (UIntArray.undef_full r__mp_d size )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_realloc_safety_wit_1_preserving : mpz_realloc_safety_wit_1_preserving.
Axiom proof_of_mpz_realloc_safety_wit_2_raw : mpz_realloc_safety_wit_2_raw.
Axiom proof_of_mpz_realloc_safety_wit_3_raw : mpz_realloc_safety_wit_3_raw.
Axiom proof_of_mpz_realloc_safety_wit_4_raw : mpz_realloc_safety_wit_4_raw.
Axiom proof_of_mpz_realloc_safety_wit_5_preserving : mpz_realloc_safety_wit_5_preserving.
Axiom proof_of_mpz_realloc_safety_wit_6_preserving : mpz_realloc_safety_wit_6_preserving.
Axiom proof_of_mpz_realloc_return_wit_1_preserving : mpz_realloc_return_wit_1_preserving.
Axiom proof_of_mpz_realloc_return_wit_2_raw : mpz_realloc_return_wit_2_raw.
Axiom proof_of_mpz_realloc_return_wit_3_preserving : mpz_realloc_return_wit_3_preserving.
Axiom proof_of_mpz_realloc_return_wit_4_raw : mpz_realloc_return_wit_4_raw.
Axiom proof_of_mpz_realloc_return_wit_5_preserving : mpz_realloc_return_wit_5_preserving.
Axiom proof_of_mpz_realloc_return_wit_6_preserving : mpz_realloc_return_wit_6_preserving.
Axiom proof_of_mpz_realloc_partial_solve_wit_1_preserving : mpz_realloc_partial_solve_wit_1_preserving.
Axiom proof_of_mpz_realloc_partial_solve_wit_2_raw : mpz_realloc_partial_solve_wit_2_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_3_raw : mpz_realloc_partial_solve_wit_3_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_4_raw_pure : mpz_realloc_partial_solve_wit_4_raw_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_4_raw : mpz_realloc_partial_solve_wit_4_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_preserving_pure : mpz_realloc_partial_solve_wit_5_preserving_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_preserving : mpz_realloc_partial_solve_wit_5_preserving.
Axiom proof_of_mpz_realloc_partial_solve_wit_6_raw : mpz_realloc_partial_solve_wit_6_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_7_raw_pure : mpz_realloc_partial_solve_wit_7_raw_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_7_raw : mpz_realloc_partial_solve_wit_7_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_8_preserving_pure : mpz_realloc_partial_solve_wit_8_preserving_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_8_preserving : mpz_realloc_partial_solve_wit_8_preserving.
Axiom proof_of_mpz_realloc_partial_solve_wit_9_raw_pure : mpz_realloc_partial_solve_wit_9_raw_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_9_raw : mpz_realloc_partial_solve_wit_9_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_10_preserving_pure : mpz_realloc_partial_solve_wit_10_preserving_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_10_preserving : mpz_realloc_partial_solve_wit_10_preserving.
Axiom proof_of_mpz_realloc_partial_solve_wit_11_raw_pure : mpz_realloc_partial_solve_wit_11_raw_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_11_raw : mpz_realloc_partial_solve_wit_11_raw.
Axiom proof_of_mpz_realloc_partial_solve_wit_12_preserving_pure : mpz_realloc_partial_solve_wit_12_preserving_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_12_preserving : mpz_realloc_partial_solve_wit_12_preserving.
Axiom proof_of_mpz_realloc_which_implies_wit_1 : mpz_realloc_which_implies_wit_1.
Axiom proof_of_mpz_realloc_which_implies_wit_2 : mpz_realloc_which_implies_wit_2.

End VC_Correct.
