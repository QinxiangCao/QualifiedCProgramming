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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_lshift_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_lshift_safety_wit_1_inplace : mpn_lshift_safety_wit_1_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_2_nonalias : mpn_lshift_safety_wit_2_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_3_inplace : mpn_lshift_safety_wit_3_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_4_inplace : mpn_lshift_safety_wit_4_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_5_nonalias : mpn_lshift_safety_wit_5_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_6_nonalias : mpn_lshift_safety_wit_6_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_7_inplace : mpn_lshift_safety_wit_7_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_8_nonalias : mpn_lshift_safety_wit_8_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_9_inplace : mpn_lshift_safety_wit_9_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_10_nonalias : mpn_lshift_safety_wit_10_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_11_inplace_inv : mpn_lshift_safety_wit_11_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_12_nonalias_inv : mpn_lshift_safety_wit_12_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_13_inplace_inv : mpn_lshift_safety_wit_13_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_14_inplace_inv : mpn_lshift_safety_wit_14_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_15_nonalias_inv : mpn_lshift_safety_wit_15_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_16_nonalias_inv : mpn_lshift_safety_wit_16_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_17_nonalias_inv : mpn_lshift_safety_wit_17_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_18_inplace_inv : mpn_lshift_safety_wit_18_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_19_inplace_inv : mpn_lshift_safety_wit_19_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_20_nonalias_inv : mpn_lshift_safety_wit_20_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_21_inplace_inv : mpn_lshift_safety_wit_21_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_22_nonalias_inv : mpn_lshift_safety_wit_22_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_23_inplace_inv : mpn_lshift_safety_wit_23_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_24_nonalias_inv : mpn_lshift_safety_wit_24_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_25_inplace_inv : mpn_lshift_safety_wit_25_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_safety_wit_26_nonalias_inv : mpn_lshift_safety_wit_26_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_entail_wit_1_nonalias : mpn_lshift_entail_wit_1_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_entail_wit_2_inplace : mpn_lshift_entail_wit_2_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_entail_wit_5_inplace_inv : mpn_lshift_entail_wit_5_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_entail_wit_6_nonalias_inv : mpn_lshift_entail_wit_6_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_1_inplace : mpn_lshift_partial_solve_wit_1_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_2_nonalias : mpn_lshift_partial_solve_wit_2_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_3_nonalias_pure : mpn_lshift_partial_solve_wit_3_nonalias_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_3_nonalias : mpn_lshift_partial_solve_wit_3_nonalias.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_4_inplace_pure : mpn_lshift_partial_solve_wit_4_inplace_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_4_inplace : mpn_lshift_partial_solve_wit_4_inplace.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_5_inplace_inv : mpn_lshift_partial_solve_wit_5_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_6_nonalias_inv : mpn_lshift_partial_solve_wit_6_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_7_nonalias_inv_pure : mpn_lshift_partial_solve_wit_7_nonalias_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_7_nonalias_inv : mpn_lshift_partial_solve_wit_7_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_8_inplace_inv_pure : mpn_lshift_partial_solve_wit_8_inplace_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_8_inplace_inv : mpn_lshift_partial_solve_wit_8_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_9_inplace_inv : mpn_lshift_partial_solve_wit_9_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_10_nonalias_inv : mpn_lshift_partial_solve_wit_10_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_11_nonalias_inv_pure : mpn_lshift_partial_solve_wit_11_nonalias_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_11_nonalias_inv : mpn_lshift_partial_solve_wit_11_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_12_inplace_inv_pure : mpn_lshift_partial_solve_wit_12_inplace_inv_pure.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_12_inplace_inv : mpn_lshift_partial_solve_wit_12_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_13_inplace_inv : mpn_lshift_partial_solve_wit_13_inplace_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_partial_solve_wit_14_nonalias_inv : mpn_lshift_partial_solve_wit_14_nonalias_inv.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_which_implies_wit_1 : mpn_lshift_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_which_implies_wit_3 : mpn_lshift_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_which_implies_wit_5 : mpn_lshift_which_implies_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_lshift_which_implies_wit_6 : mpn_lshift_which_implies_wit_6.
Proof. Admitted. 

