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
From SimpleC.EE.Applications_human.minigmp Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_gmp_abs_safety_wit_1 : gmp_abs_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_abs_safety_wit_2 : gmp_abs_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_1 : gmp_cmp_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_2 : gmp_cmp_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_3 : gmp_cmp_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_4 : gmp_cmp_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_return_wit_1 : gmp_cmp_return_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_return_wit_2 : gmp_cmp_return_wit_2.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_return_wit_3 : gmp_cmp_return_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_safety_wit_2 : mpn_copyi_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_partial_solve_wit_1 : mpn_copyi_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_partial_solve_wit_2 : mpn_copyi_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_partial_solve_wit_3 : mpn_copyi_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_2 : mpn_cmp_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_3 : mpn_cmp_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_4 : mpn_cmp_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_5 : mpn_cmp_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_6 : mpn_cmp_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_7 : mpn_cmp_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_1 : mpn_cmp_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_2 : mpn_cmp_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_3 : mpn_cmp_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_4 : mpn_cmp_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_5 : mpn_cmp_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_safety_wit_1 : mpn_cmp4_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_safety_wit_2 : mpn_cmp4_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_safety_wit_3 : mpn_cmp4_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_partial_solve_wit_1_pure : mpn_cmp4_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_partial_solve_wit_1 : mpn_cmp4_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_1 : mpn_add_1_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_2 : mpn_add_1_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_3 : mpn_add_1_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_4 : mpn_add_1_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_5 : mpn_add_1_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_1 : mpn_add_1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_2 : mpn_add_1_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_3 : mpn_add_1_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_4 : mpn_add_1_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_5 : mpn_add_1_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_6 : mpn_add_1_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_7 : mpn_add_1_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_1 : mpn_add_n_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_2 : mpn_add_n_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_3 : mpn_add_n_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_4 : mpn_add_n_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_5 : mpn_add_n_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_6 : mpn_add_n_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_1 : mpn_add_n_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_2 : mpn_add_n_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_3 : mpn_add_n_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_4 : mpn_add_n_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_5 : mpn_add_n_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_6 : mpn_add_n_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_7 : mpn_add_n_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_add_safety_wit_1 : mpn_add_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_entail_wit_1 : mpn_add_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_1_pure : mpn_add_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_1 : mpn_add_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_2_pure : mpn_add_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_2 : mpn_add_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_3_pure : mpn_add_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_3 : mpn_add_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_4 : mpn_add_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_5_pure : mpn_add_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_5 : mpn_add_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_1 : gmp_umul_ppmm_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_2 : gmp_umul_ppmm_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_3 : gmp_umul_ppmm_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_4 : gmp_umul_ppmm_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_5 : gmp_umul_ppmm_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_6 : gmp_umul_ppmm_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_7 : gmp_umul_ppmm_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_8 : gmp_umul_ppmm_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_9 : gmp_umul_ppmm_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_10 : gmp_umul_ppmm_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_11 : gmp_umul_ppmm_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_12 : gmp_umul_ppmm_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_13 : gmp_umul_ppmm_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_14 : gmp_umul_ppmm_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_15 : gmp_umul_ppmm_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_16 : gmp_umul_ppmm_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_17 : gmp_umul_ppmm_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_18 : gmp_umul_ppmm_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_safety_wit_19 : gmp_umul_ppmm_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_entail_wit_1 : gmp_umul_ppmm_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_umul_ppmm_entail_wit_2 : gmp_umul_ppmm_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_safety_wit_1 : mpn_mul_1_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_safety_wit_2 : mpn_mul_1_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_safety_wit_3 : mpn_mul_1_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_safety_wit_4 : mpn_mul_1_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_safety_wit_5 : mpn_mul_1_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_safety_wit_6 : mpn_mul_1_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_entail_wit_2 : mpn_mul_1_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_entail_wit_3 : mpn_mul_1_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_entail_wit_4 : mpn_mul_1_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_partial_solve_wit_1 : mpn_mul_1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_partial_solve_wit_2 : mpn_mul_1_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_partial_solve_wit_3 : mpn_mul_1_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_mul_1_partial_solve_wit_4 : mpn_mul_1_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_safety_wit_1 : mpn_sub_1_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_safety_wit_2 : mpn_sub_1_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_safety_wit_3 : mpn_sub_1_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_safety_wit_4 : mpn_sub_1_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_safety_wit_5 : mpn_sub_1_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_1 : mpn_sub_1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_2 : mpn_sub_1_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_3 : mpn_sub_1_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_4 : mpn_sub_1_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_5 : mpn_sub_1_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_6 : mpn_sub_1_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_sub_1_partial_solve_wit_7 : mpn_sub_1_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_safety_wit_1 : mpn_sub_n_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_safety_wit_2 : mpn_sub_n_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_safety_wit_3 : mpn_sub_n_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_safety_wit_4 : mpn_sub_n_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_safety_wit_5 : mpn_sub_n_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_safety_wit_6 : mpn_sub_n_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_1 : mpn_sub_n_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_2 : mpn_sub_n_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_3 : mpn_sub_n_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_4 : mpn_sub_n_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_5 : mpn_sub_n_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_6 : mpn_sub_n_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_sub_n_partial_solve_wit_7 : mpn_sub_n_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_sub_safety_wit_1 : mpn_sub_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_entail_wit_1 : mpn_sub_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_entail_wit_2 : mpn_sub_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_1_pure : mpn_sub_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_1 : mpn_sub_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_2_pure : mpn_sub_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_2 : mpn_sub_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_3_pure : mpn_sub_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_3 : mpn_sub_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_4 : mpn_sub_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_5_pure : mpn_sub_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_mpn_sub_partial_solve_wit_5 : mpn_sub_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_clear_return_wit_1 : mpz_clear_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_1 : mpz_realloc_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_2 : mpz_realloc_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_3 : mpz_realloc_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_return_wit_2 : mpz_realloc_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_1 : mpz_realloc_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_2 : mpz_realloc_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_3 : mpz_realloc_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_4 : mpz_realloc_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_5 : mpz_realloc_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1 : mrz_realloc_if_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_safety_wit_1 : mpz_sgn_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_partial_solve_wit_1 : mpz_sgn_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_partial_solve_wit_2 : mpz_sgn_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_swap_return_wit_1 : mpz_swap_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_1 : mpz_swap_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_2 : mpz_swap_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_3 : mpz_swap_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_safety_wit_2 : mpz_abs_add_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_1 : mpz_abs_add_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_2 : mpz_abs_add_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_3 : mpz_abs_add_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_4 : mpz_abs_add_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_5 : mpz_abs_add_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_6 : mpz_abs_add_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_7 : mpz_abs_add_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_8 : mpz_abs_add_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_abs_add_partial_solve_wit_9 : mpz_abs_add_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_1 : mpz_abs_sub_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_2 : mpz_abs_sub_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_3 : mpz_abs_sub_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_4 : mpz_abs_sub_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_5 : mpz_abs_sub_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_6 : mpz_abs_sub_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_7 : mpz_abs_sub_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_8 : mpz_abs_sub_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_9 : mpz_abs_sub_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_10 : mpz_abs_sub_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_11 : mpz_abs_sub_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_safety_wit_12 : mpz_abs_sub_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_1 : mpz_abs_sub_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_2 : mpz_abs_sub_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_3 : mpz_abs_sub_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_4 : mpz_abs_sub_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5 : mpz_abs_sub_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_6 : mpz_abs_sub_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7 : mpz_abs_sub_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8 : mpz_abs_sub_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9 : mpz_abs_sub_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_10 : mpz_abs_sub_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11 : mpz_abs_sub_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_mpz_add_safety_wit_1 : mpz_add_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_add_safety_wit_2 : mpz_add_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_add_safety_wit_4 : mpz_add_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_1 : mpz_add_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_2 : mpz_add_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_3 : mpz_add_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_4 : mpz_add_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_5 : mpz_add_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_6 : mpz_add_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_7 : mpz_add_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_8 : mpz_add_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_9 : mpz_add_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_add_partial_solve_wit_10 : mpz_add_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_mpz_sub_safety_wit_1 : mpz_sub_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sub_safety_wit_2 : mpz_sub_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_sub_safety_wit_4 : mpz_sub_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_1 : mpz_sub_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_2 : mpz_sub_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_3 : mpz_sub_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_4 : mpz_sub_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_5 : mpz_sub_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_6 : mpz_sub_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_7 : mpz_sub_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_8 : mpz_sub_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_9 : mpz_sub_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_sub_partial_solve_wit_10 : mpz_sub_partial_solve_wit_10.
Proof. Admitted. 

