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

(*----- Function mpz_realloc -----*)

Definition mpz_realloc_safety_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (size_pre >= cap_raw)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) ,
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

Definition mpz_realloc_safety_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ False ”
.

Definition mpz_realloc_safety_wit_3 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)) ,
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

Definition mpz_realloc_return_wit_1 := 
(
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (size_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (UIntArray.undef_full ptr_raw cap_raw )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_1_split_goal_spatial := 
forall (size_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (UIntArray.undef_full ptr_raw cap_raw )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_2 := 
(
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (UIntArray.undef_full retval retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (size_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)) ,
  (UIntArray.undef_full retval retval_2 )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_2_split_goal_spatial := 
forall (size_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (sz_raw)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap_raw)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH9 : (cap_raw <> 0)) ,
  (UIntArray.undef_full retval retval_2 )
|--
  (UIntArray.undef_full retval (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_partial_solve_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (size_pre >= cap_raw)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) ,
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

Definition mpz_realloc_partial_solve_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)) ,
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

Definition mpz_realloc_partial_solve_wit_3_pure := 
(
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)) ,
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
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cap_raw >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw <> 0)) ,
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

Definition mpz_realloc_partial_solve_wit_3_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cap_raw >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw <> 0)) ,
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

Definition mpz_realloc_partial_solve_wit_3_aux := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)) ,
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

Definition mpz_realloc_partial_solve_wit_3 := mpz_realloc_partial_solve_wit_3_pure -> mpz_realloc_partial_solve_wit_3_aux.

Definition mpz_realloc_partial_solve_wit_4 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)) ,
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

Definition mpz_realloc_partial_solve_wit_5_pure := 
(
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)) ,
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
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_raw >= INT_MIN)) (PreH4 : (sz_raw >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw = 0)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval >= 0) ”
).

Definition mpz_realloc_partial_solve_wit_5_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap_raw >= INT_MIN)) (PreH4 : (sz_raw >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap_raw)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap_raw >= 0)) (PreH10 : (cap_raw <= INT_MAX)) (PreH11 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH12 : (cap_raw = 0)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ (retval >= 0) ”
.

Definition mpz_realloc_partial_solve_wit_5_aux := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)) ,
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

Definition mpz_realloc_partial_solve_wit_5 := mpz_realloc_partial_solve_wit_5_pure -> mpz_realloc_partial_solve_wit_5_aux.

Definition mpz_realloc_partial_solve_wit_6_pure := 
(
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)) ,
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
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (INT_MIN < sz_raw) ”
).

Definition mpz_realloc_partial_solve_wit_6_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.undef_full retval_2 retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
|--
  “ (INT_MIN < sz_raw) ”
.

Definition mpz_realloc_partial_solve_wit_6_aux := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw <> 0)) ,
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

Definition mpz_realloc_partial_solve_wit_6 := mpz_realloc_partial_solve_wit_6_pure -> mpz_realloc_partial_solve_wit_6_aux.

Definition mpz_realloc_partial_solve_wit_7_pure := 
(
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)) ,
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
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw = 0)) ,
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

Definition mpz_realloc_partial_solve_wit_7_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap_raw)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap_raw >= 0)) (PreH9 : (cap_raw <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH11 : (cap_raw = 0)) ,
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

Definition mpz_realloc_partial_solve_wit_7_aux := 
forall (size_pre: Z) (r_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap_raw)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap_raw >= 0)) (PreH5 : (cap_raw <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (size_pre) (1)))) (PreH7 : (cap_raw = 0)) ,
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

Definition mpz_realloc_partial_solve_wit_7 := mpz_realloc_partial_solve_wit_7_pure -> mpz_realloc_partial_solve_wit_7_aux.

Definition mpz_realloc_which_implies_wit_1 := 
(
forall (r: Z) (r__mp_alloc: Z) (r__mp_d: Z) ,
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
forall (r__mp_d: Z) ,
  TT && emp 
|--
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
).

Definition mpz_realloc_which_implies_wit_1_split_goal_spatial := 
forall (r__mp_d: Z) ,
  TT && emp 
|--
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
.

Definition mpz_realloc_which_implies_wit_2 := 
(
forall (r: Z) (r__mp_d: Z) (size: Z) ,
  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  (UIntArray.undef_seg r__mp_d 0 size )
|--
  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_full r__mp_d size )
) \/
(
forall (r__mp_d: Z) (size: Z) ,
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  (UIntArray.undef_seg r__mp_d 0 size )
|--
  (UIntArray.undef_full r__mp_d size )
).

Definition mpz_realloc_which_implies_wit_2_split_goal_spatial := 
forall (r__mp_d: Z) (size: Z) ,
  (mpd_store_Z_compact UINT_MOD r__mp_d 0 0 )
  **  (UIntArray.undef_seg r__mp_d 0 size )
|--
  (UIntArray.undef_full r__mp_d size )
.

(*----- Function mrz_realloc_if -----*)

Definition mrz_realloc_if_return_wit_1 := 
(
forall (n_pre: Z) (z_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (z_pre__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full ptr_raw (Z.max (n_pre) (cap_raw)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
) \/
(
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ” 
  &&  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full ptr_raw (Z.max (n_pre) (cap_raw)) )
).

Definition mrz_realloc_if_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  “ (cap_raw = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre <= cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full ptr_raw cap_raw )
|--
  (UIntArray.undef_full ptr_raw (Z.max (n_pre) (cap_raw)) )
.

Definition mrz_realloc_if_return_wit_2 := 
(
forall (n_pre: Z) (z_pre: Z) (cap_raw: Z) (sz_raw: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_callee__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (z_pre__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full retval (Z.max (n_pre) (cap_raw)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap_raw))) ” 
  &&  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
  &&  (UIntArray.undef_full retval (Z.max (n_pre) (cap_raw)) )
).

Definition mrz_realloc_if_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_2_split_goal_2 := 
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap_raw))) ”
.

Definition mrz_realloc_if_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (cap_raw: Z) (sz_raw: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH2 : (n_pre > cap_raw)) (PreH3 : (cap_raw >= 0)) (PreH4 : (cap_raw <= INT_MAX)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  (UIntArray.undef_full retval (Z.max (n_pre) (1)) )
|--
  (UIntArray.undef_full retval (Z.max (n_pre) (cap_raw)) )
.

Definition mrz_realloc_if_partial_solve_wit_1_pure := 
(
forall (n_pre: Z) (z_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre > cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
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
forall (n_pre: Z) (z_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (cap_raw >= INT_MIN)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre > cap_raw)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (1))) ”
).

Definition mrz_realloc_if_partial_solve_wit_1_pure_split_goal_1 := 
forall (n_pre: Z) (z_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (sz_raw <= INT_MAX)) (PreH2 : (cap_raw >= INT_MIN)) (PreH3 : (sz_raw >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre > cap_raw)) (PreH6 : (cap_raw >= 0)) (PreH7 : (cap_raw <= INT_MAX)) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.undef_full ptr_raw cap_raw )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_raw)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_raw)
|--
  “ ((Zabs (sz_raw)) <= (Z.max (n_pre) (1))) ”
.

Definition mrz_realloc_if_partial_solve_wit_1_aux := 
forall (n_pre: Z) (z_pre: Z) (cap_raw: Z) (sz_raw: Z) (ptr_raw: Z) (PreH1 : (n_pre > cap_raw)) (PreH2 : (cap_raw >= 0)) (PreH3 : (cap_raw <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (sz_raw)) <= (Z.max (n_pre) (cap_raw)))) ,
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

Definition mrz_realloc_if_partial_solve_wit_1 := mrz_realloc_if_partial_solve_wit_1_pure -> mrz_realloc_if_partial_solve_wit_1_aux.

(*----- Function mpz_set_ui -----*)

Definition mpz_set_ui_safety_wit_1 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre = x0)) (PreH2 : (0 <= x0)) ,
  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_set_ui_safety_wit_2 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre = x0)) (PreH3 : (0 <= x0)) ,
  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_set_ui_safety_wit_3 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre = x0)) (PreH3 : (same_sign old size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (cap >= 0)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_set_ui_safety_wit_4 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_set_ui_safety_wit_5 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_set_ui_safety_wit_6 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_addr_v)
  **  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_set_ui_safety_wit_7 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (x_pre = x0)) (PreH3 : (0 <= x0)) ,
  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  (store_Z r_pre old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_set_ui_entail_wit_1 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (x_pre > 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old)) (Zabs (size_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (x_pre > 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (1)) <= (Z.max (1) (cap))) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
) \/
(
forall (x_pre: Z) (x0: Z) (old: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign old size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (x_pre > 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (old)) (Zabs (size_2)) )
|--
  EX (size: Z) ,
  “ (x_pre > 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (cap_2 >= 0) ” 
  &&  “ (cap_2 <= INT_MAX) ” 
  &&  “ ((Zabs (1)) <= (Z.max (1) (cap_2))) ”
  &&  (UIntArray.undef_full ptr_2 cap_2 )
).

Definition mpz_set_ui_entail_wit_2 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (cap_new: Z) ,
  “ (cap_new = (Z.max (1) (cap))) ” 
  &&  “ (x_pre > 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (cap_new >= 1) ” 
  &&  “ (cap_new <= INT_MAX) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  (UIntArray.undef_seg retval 0 1 )
  **  (UIntArray.undef_seg retval 1 cap_new )
) \/
(
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  “ (z_callee__mp_alloc <= INT_MAX) ” 
  &&  “ (z_callee__mp_alloc >= 1) ”
  &&  (UIntArray.undef_seg retval 0 1 )
  **  (UIntArray.undef_seg retval 1 (Z.max (1) (cap)) )
).

Definition mpz_set_ui_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  “ (z_callee__mp_alloc <= INT_MAX) ”
.

Definition mpz_set_ui_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  “ (z_callee__mp_alloc >= 1) ”
.

Definition mpz_set_ui_entail_wit_2_split_goal_spatial := 
forall (x_pre: Z) (x0: Z) (old: Z) (size: Z) (cap: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (z_callee__mp_alloc = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (same_sign old size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  (UIntArray.undef_full retval (Z.max (1) (cap)) )
|--
  (UIntArray.undef_seg retval 0 1 )
  **  (UIntArray.undef_seg retval 1 (Z.max (1) (cap)) )
.

Definition mpz_set_ui_return_wit_1 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  (store_Z r_pre x0 )
) \/
(
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (x_pre <= UINT_MAX)) (PreH2 : (x_pre >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre > 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ ((Zabs (1)) <= cap_new) ” 
  &&  “ (same_sign x_pre 1 ) ”
  &&  (UIntArray.undef_seg rp_addr_v (Zabs (1)) cap_new )
  **  (mpd_store_Z_compact UINT_MOD rp_addr_v (Zabs (x0)) (Zabs (1)) )
).

Definition mpz_set_ui_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (x_pre <= UINT_MAX)) (PreH2 : (x_pre >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre > 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ ((Zabs (1)) <= cap_new) ”
.

Definition mpz_set_ui_return_wit_1_split_goal_2 := 
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (x_pre <= UINT_MAX)) (PreH2 : (x_pre >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre > 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (same_sign x_pre 1 ) ”
.

Definition mpz_set_ui_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (x_pre <= UINT_MAX)) (PreH2 : (x_pre >= 0)) (PreH3 : (cap_new = (Z.max (1) (cap)))) (PreH4 : (x_pre > 0)) (PreH5 : (x_pre = x0)) (PreH6 : (cap_new >= 1)) (PreH7 : (cap_new <= INT_MAX)) ,
  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |-> x_pre)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  (UIntArray.undef_seg rp_addr_v (Zabs (1)) cap_new )
  **  (mpd_store_Z_compact UINT_MOD rp_addr_v (Zabs (x0)) (Zabs (1)) )
.

Definition mpz_set_ui_return_wit_2 := 
(
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign old size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (x_pre <= 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (store_Z r_pre x0 )
) \/
(
forall (x_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign old size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (x_pre <= 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
|--
  “ ((Zabs (0)) <= cap) ” 
  &&  “ (same_sign x_pre 0 ) ”
  &&  (UIntArray.undef_seg ptr (Zabs (0)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (x0)) (Zabs (0)) )
).

Definition mpz_set_ui_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign old size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (x_pre <= 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
|--
  “ ((Zabs (0)) <= cap) ”
.

Definition mpz_set_ui_return_wit_2_split_goal_2 := 
forall (x_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign old size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (x_pre <= 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
|--
  “ (same_sign x_pre 0 ) ”
.

Definition mpz_set_ui_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign old size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (x_pre <= 0)) (PreH4 : (x_pre = x0)) (PreH5 : (0 <= x0)) ,
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
|--
  (UIntArray.undef_seg ptr (Zabs (0)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (x0)) (Zabs (0)) )
.

Definition mpz_set_ui_partial_solve_wit_1 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre = x0)) (PreH3 : (0 <= x0)) ,
  (store_Z r_pre old )
|--
  EX (ptr: Z)  (size: Z)  (cap: Z) ,
  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (x_pre > 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (0 <= x0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_set_ui_partial_solve_wit_2_pure := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre = x0)) (PreH3 : (same_sign old size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (cap >= 0)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "LOCAL_GMP_LIMB_BITS" ) )) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((Zabs (1)) <= (Z.max (1) (cap))) ”
.

Definition mpz_set_ui_partial_solve_wit_2_aux := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre = x0)) (PreH3 : (same_sign old size )) (PreH4 : ((Zabs (size)) <= cap)) (PreH5 : (cap >= 0)) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zabs (1)) <= (Z.max (1) (cap)))) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((Zabs (1)) <= (Z.max (1) (cap))) ” 
  &&  “ (x_pre > 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (1)) <= (Z.max (1) (cap))) ”
  &&  (UIntArray.undef_full ptr cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_set_ui_partial_solve_wit_2 := mpz_set_ui_partial_solve_wit_2_pure -> mpz_set_ui_partial_solve_wit_2_aux.

Definition mpz_set_ui_partial_solve_wit_3 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (cap: Z) (cap_new: Z) (rp_addr_v: Z) (PreH1 : (cap_new = (Z.max (1) (cap)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre = x0)) (PreH4 : (cap_new >= 1)) (PreH5 : (cap_new <= INT_MAX)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 0 1 )
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
|--
  “ (cap_new = (Z.max (1) (cap))) ” 
  &&  “ (x_pre > 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (cap_new >= 1) ” 
  &&  “ (cap_new <= INT_MAX) ”
  &&  (((rp_addr_v + (0 * sizeof(UINT)))) # UInt  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 1)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_new)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rp_addr_v)
  **  (UIntArray.undef_seg rp_addr_v 1 cap_new )
.

Definition mpz_set_ui_partial_solve_wit_4 := 
forall (x_pre: Z) (r_pre: Z) (x0: Z) (old: Z) (PreH1 : (x_pre <= 0)) (PreH2 : (x_pre = x0)) (PreH3 : (0 <= x0)) ,
  (store_Z r_pre old )
|--
  EX (ptr: Z)  (size: Z)  (cap: Z) ,
  “ (same_sign old size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (x_pre <= 0) ” 
  &&  “ (x_pre = x0) ” 
  &&  “ (0 <= x0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (old)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_realloc_safety_wit_1 : mpz_realloc_safety_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_2 : mpz_realloc_safety_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_3 : mpz_realloc_safety_wit_3.
Axiom proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Axiom proof_of_mpz_realloc_return_wit_2 : mpz_realloc_return_wit_2.
Axiom proof_of_mpz_realloc_partial_solve_wit_1 : mpz_realloc_partial_solve_wit_1.
Axiom proof_of_mpz_realloc_partial_solve_wit_2 : mpz_realloc_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_3 : mpz_realloc_partial_solve_wit_3.
Axiom proof_of_mpz_realloc_partial_solve_wit_4 : mpz_realloc_partial_solve_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_5 : mpz_realloc_partial_solve_wit_5.
Axiom proof_of_mpz_realloc_partial_solve_wit_6_pure : mpz_realloc_partial_solve_wit_6_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_6 : mpz_realloc_partial_solve_wit_6.
Axiom proof_of_mpz_realloc_partial_solve_wit_7_pure : mpz_realloc_partial_solve_wit_7_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_7 : mpz_realloc_partial_solve_wit_7.
Axiom proof_of_mpz_realloc_which_implies_wit_1 : mpz_realloc_which_implies_wit_1.
Axiom proof_of_mpz_realloc_which_implies_wit_2 : mpz_realloc_which_implies_wit_2.
Axiom proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Axiom proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1 : mrz_realloc_if_partial_solve_wit_1.
Axiom proof_of_mpz_set_ui_safety_wit_1 : mpz_set_ui_safety_wit_1.
Axiom proof_of_mpz_set_ui_safety_wit_2 : mpz_set_ui_safety_wit_2.
Axiom proof_of_mpz_set_ui_safety_wit_3 : mpz_set_ui_safety_wit_3.
Axiom proof_of_mpz_set_ui_safety_wit_4 : mpz_set_ui_safety_wit_4.
Axiom proof_of_mpz_set_ui_safety_wit_5 : mpz_set_ui_safety_wit_5.
Axiom proof_of_mpz_set_ui_safety_wit_6 : mpz_set_ui_safety_wit_6.
Axiom proof_of_mpz_set_ui_safety_wit_7 : mpz_set_ui_safety_wit_7.
Axiom proof_of_mpz_set_ui_entail_wit_1 : mpz_set_ui_entail_wit_1.
Axiom proof_of_mpz_set_ui_entail_wit_2 : mpz_set_ui_entail_wit_2.
Axiom proof_of_mpz_set_ui_return_wit_1 : mpz_set_ui_return_wit_1.
Axiom proof_of_mpz_set_ui_return_wit_2 : mpz_set_ui_return_wit_2.
Axiom proof_of_mpz_set_ui_partial_solve_wit_1 : mpz_set_ui_partial_solve_wit_1.
Axiom proof_of_mpz_set_ui_partial_solve_wit_2_pure : mpz_set_ui_partial_solve_wit_2_pure.
Axiom proof_of_mpz_set_ui_partial_solve_wit_2 : mpz_set_ui_partial_solve_wit_2.
Axiom proof_of_mpz_set_ui_partial_solve_wit_3 : mpz_set_ui_partial_solve_wit_3.
Axiom proof_of_mpz_set_ui_partial_solve_wit_4 : mpz_set_ui_partial_solve_wit_4.

End VC_Correct.
