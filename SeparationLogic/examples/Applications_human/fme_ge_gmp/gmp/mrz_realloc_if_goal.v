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

(*----- Function mrz_realloc_if -----*)

Definition mrz_realloc_if_return_wit_1 := 
(
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (z_pre__mp_alloc = (Z.max (n_pre) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max (n_pre) (cap)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
) \/
(
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (cap = (Z.max (n_pre) (cap))) ” 
  &&  “ (cap = (Z.max (n_pre) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max (n_pre) (cap)) )
).

Definition mrz_realloc_if_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (cap = (Z.max (n_pre) (cap))) ”
.

Definition mrz_realloc_if_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (cap = (Z.max (n_pre) (cap))) ”
.

Definition mrz_realloc_if_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max (n_pre) (cap)) )
.

Definition mrz_realloc_if_return_wit_2 := 
(
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_callee__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (z_pre__mp_alloc = (Z.max (n_pre) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (cap)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap))) ” 
  &&  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (cap)) )
).

Definition mrz_realloc_if_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap))) ”
.

Definition mrz_realloc_if_return_wit_2_split_goal_2 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max (n_pre) (cap))) ”
.

Definition mrz_realloc_if_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (cap)) )
.

Definition mrz_realloc_if_partial_solve_wit_1_pure := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre > cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (n_pre >= cap) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
.

Definition mrz_realloc_if_partial_solve_wit_1_aux := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre > cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (n_pre >= cap) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ” 
  &&  “ (n_pre > cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mrz_realloc_if_partial_solve_wit_1 := mrz_realloc_if_partial_solve_wit_1_pure -> mrz_realloc_if_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Axiom proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1 : mrz_realloc_if_partial_solve_wit_1.

End VC_Correct.
