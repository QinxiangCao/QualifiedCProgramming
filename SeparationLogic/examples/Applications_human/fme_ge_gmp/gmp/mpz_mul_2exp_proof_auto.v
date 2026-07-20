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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_mul_2exp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_copyd_safety_wit_1 : mpn_copyd_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_safety_wit_2_off_zero : mpn_copyd_safety_wit_2_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_safety_wit_3_off_pos : mpn_copyd_safety_wit_3_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_safety_wit_4_off_zero : mpn_copyd_safety_wit_4_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_safety_wit_5_off_pos : mpn_copyd_safety_wit_5_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_safety_wit_6_off_zero : mpn_copyd_safety_wit_6_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_safety_wit_7_off_pos : mpn_copyd_safety_wit_7_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_entail_wit_1_off_zero : mpn_copyd_entail_wit_1_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_entail_wit_3_off_zero : mpn_copyd_entail_wit_3_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_entail_wit_4_off_pos : mpn_copyd_entail_wit_4_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_1 : mpn_copyd_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_2_off_zero_pure : mpn_copyd_partial_solve_wit_2_off_zero_pure.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_2_off_zero : mpn_copyd_partial_solve_wit_2_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_3_off_pos_pure : mpn_copyd_partial_solve_wit_3_off_pos_pure.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_3_off_pos : mpn_copyd_partial_solve_wit_3_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_4_off_zero : mpn_copyd_partial_solve_wit_4_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_5_off_zero : mpn_copyd_partial_solve_wit_5_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_6_off_pos : mpn_copyd_partial_solve_wit_6_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_copyd_partial_solve_wit_7_off_pos : mpn_copyd_partial_solve_wit_7_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_zero_safety_wit_1 : mpn_zero_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_zero_safety_wit_2 : mpn_zero_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_zero_safety_wit_3 : mpn_zero_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_zero_safety_wit_4 : mpn_zero_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_zero_partial_solve_wit_1 : mpn_zero_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_zero_partial_solve_wit_2_pure : mpn_zero_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_mpn_zero_partial_solve_wit_2 : mpn_zero_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_zero_partial_solve_wit_3 : mpn_zero_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_zero_which_implies_wit_1 : mpn_zero_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_zero_which_implies_wit_2 : mpn_zero_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_1 : mpn_lshift_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_2_off_zero : mpn_lshift_safety_wit_2_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_3_off_pos : mpn_lshift_safety_wit_3_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_4_off_zero : mpn_lshift_safety_wit_4_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_5_off_zero : mpn_lshift_safety_wit_5_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_6_off_pos : mpn_lshift_safety_wit_6_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_7_off_pos : mpn_lshift_safety_wit_7_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_8_off_zero : mpn_lshift_safety_wit_8_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_9_off_pos : mpn_lshift_safety_wit_9_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_10_off_zero : mpn_lshift_safety_wit_10_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_11_off_pos : mpn_lshift_safety_wit_11_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_12_off_zero_inv : mpn_lshift_safety_wit_12_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_13_off_pos_inv : mpn_lshift_safety_wit_13_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_14_off_zero_inv : mpn_lshift_safety_wit_14_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_15_off_zero_inv : mpn_lshift_safety_wit_15_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_16_off_pos_inv : mpn_lshift_safety_wit_16_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_17_off_pos_inv : mpn_lshift_safety_wit_17_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_18_off_pos_inv : mpn_lshift_safety_wit_18_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_19_off_zero_inv : mpn_lshift_safety_wit_19_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_20_off_zero_inv : mpn_lshift_safety_wit_20_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_21_off_pos_inv : mpn_lshift_safety_wit_21_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_22_off_zero_inv : mpn_lshift_safety_wit_22_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_23_off_pos_inv : mpn_lshift_safety_wit_23_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_24_off_zero_inv : mpn_lshift_safety_wit_24_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_25_off_pos_inv : mpn_lshift_safety_wit_25_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_26_off_zero_inv : mpn_lshift_safety_wit_26_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_27_off_pos_inv : mpn_lshift_safety_wit_27_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_entail_wit_3_off_zero_inv : mpn_lshift_entail_wit_3_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_entail_wit_4_off_pos_inv : mpn_lshift_entail_wit_4_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_1 : mpn_lshift_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_2_off_zero : mpn_lshift_partial_solve_wit_2_off_zero.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_3_off_pos : mpn_lshift_partial_solve_wit_3_off_pos.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_4_off_zero_inv : mpn_lshift_partial_solve_wit_4_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_5_off_pos_inv : mpn_lshift_partial_solve_wit_5_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_6_off_zero_inv_pure : mpn_lshift_partial_solve_wit_6_off_zero_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_6_off_zero_inv : mpn_lshift_partial_solve_wit_6_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_7_off_pos_inv_pure : mpn_lshift_partial_solve_wit_7_off_pos_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_7_off_pos_inv : mpn_lshift_partial_solve_wit_7_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_8_off_zero_inv : mpn_lshift_partial_solve_wit_8_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_9_off_pos_inv : mpn_lshift_partial_solve_wit_9_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_10_off_zero_inv_pure : mpn_lshift_partial_solve_wit_10_off_zero_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_10_off_zero_inv : mpn_lshift_partial_solve_wit_10_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_11_off_pos_inv_pure : mpn_lshift_partial_solve_wit_11_off_pos_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_11_off_pos_inv : mpn_lshift_partial_solve_wit_11_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_12_off_zero_inv : mpn_lshift_partial_solve_wit_12_off_zero_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_13_off_pos_inv : mpn_lshift_partial_solve_wit_13_off_pos_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_which_implies_wit_4 : mpn_lshift_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_1 : mpz_mul_2exp_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_2 : mpz_mul_2exp_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_3 : mpz_mul_2exp_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_4 : mpz_mul_2exp_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_5 : mpz_mul_2exp_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_6 : mpz_mul_2exp_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_10 : mpz_mul_2exp_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_11 : mpz_mul_2exp_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_12 : mpz_mul_2exp_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_13 : mpz_mul_2exp_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_14 : mpz_mul_2exp_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_15 : mpz_mul_2exp_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_16 : mpz_mul_2exp_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_17 : mpz_mul_2exp_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_18 : mpz_mul_2exp_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_19 : mpz_mul_2exp_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_20 : mpz_mul_2exp_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_21 : mpz_mul_2exp_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_22 : mpz_mul_2exp_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_23 : mpz_mul_2exp_safety_wit_23.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_24 : mpz_mul_2exp_safety_wit_24.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_safety_wit_25 : mpz_mul_2exp_safety_wit_25.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_1 : mpz_mul_2exp_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_2 : mpz_mul_2exp_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_3 : mpz_mul_2exp_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_4 : mpz_mul_2exp_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_5_pure : mpz_mul_2exp_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_5 : mpz_mul_2exp_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_6 : mpz_mul_2exp_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_7_pure : mpz_mul_2exp_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_7 : mpz_mul_2exp_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_8_pure : mpz_mul_2exp_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_8 : mpz_mul_2exp_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_9_pure : mpz_mul_2exp_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_9 : mpz_mul_2exp_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_10_pure : mpz_mul_2exp_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_10 : mpz_mul_2exp_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_11 : mpz_mul_2exp_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_12 : mpz_mul_2exp_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_13 : mpz_mul_2exp_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_14 : mpz_mul_2exp_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_15 : mpz_mul_2exp_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_16 : mpz_mul_2exp_partial_solve_wit_16.
Proof. Admitted. 

