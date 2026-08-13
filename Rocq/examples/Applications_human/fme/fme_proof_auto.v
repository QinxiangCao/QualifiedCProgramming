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
From SimpleC.EE.Applications_human.fme Require Import fme_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme.fme_lib.
Local Open Scope sac.

Lemma proof_of_gcd_safety_wit_1 : gcd_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gcd_safety_wit_2 : gcd_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_check_add_safe_safety_wit_1 : check_add_safe_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_check_add_safe_safety_wit_2 : check_add_safe_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_check_add_safe_safety_wit_3 : check_add_safe_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_check_add_safe_safety_wit_4 : check_add_safe_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_check_add_safe_safety_wit_5 : check_add_safe_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_check_add_safe_safety_wit_6 : check_add_safe_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_check_add_safe_return_wit_1 : check_add_safe_return_wit_1.
Proof. Admitted. 

Lemma proof_of_check_add_safe_return_wit_2 : check_add_safe_return_wit_2.
Proof. Admitted. 

Lemma proof_of_check_add_safe_return_wit_3 : check_add_safe_return_wit_3.
Proof. Admitted. 

Lemma proof_of_check_add_safe_return_wit_4 : check_add_safe_return_wit_4.
Proof. Admitted. 

Lemma proof_of_NilInequList_safety_wit_1 : NilInequList_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_NilInequList_return_wit_1 : NilInequList_return_wit_1.
Proof. Admitted. 

Lemma proof_of_ConsInequList_return_wit_1 : ConsInequList_return_wit_1.
Proof. Admitted. 

Lemma proof_of_ConsInequList_partial_solve_wit_1 : ConsInequList_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_free_InequList_safety_wit_1 : free_InequList_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_free_InequList_safety_wit_2 : free_InequList_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_free_InequList_safety_wit_3 : free_InequList_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_free_InequList_safety_wit_4 : free_InequList_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_free_InequList_return_wit_2 : free_InequList_return_wit_2.
Proof. Admitted. 

Lemma proof_of_free_InequList_partial_solve_wit_1 : free_InequList_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_free_InequList_partial_solve_wit_2 : free_InequList_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_free_InequList_partial_solve_wit_3 : free_InequList_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_free_InequList_partial_solve_wit_4 : free_InequList_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_free_InequList_partial_solve_wit_5 : free_InequList_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_eliminate_safety_wit_1 : eliminate_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_eliminate_safety_wit_2 : eliminate_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_eliminate_safety_wit_3 : eliminate_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_eliminate_entail_wit_1 : eliminate_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_1 : eliminate_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_2 : eliminate_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_3 : eliminate_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_4_pure : eliminate_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_4 : eliminate_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_5 : eliminate_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_eliminate_partial_solve_wit_6 : eliminate_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_eliminate_which_implies_wit_1 : eliminate_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_1 : generate_new_constr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_5 : generate_new_constr_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_7 : generate_new_constr_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_8 : generate_new_constr_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_10 : generate_new_constr_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_12 : generate_new_constr_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_13 : generate_new_constr_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_14 : generate_new_constr_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_15 : generate_new_constr_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_16 : generate_new_constr_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_17 : generate_new_constr_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_18 : generate_new_constr_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_19 : generate_new_constr_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_20 : generate_new_constr_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_21 : generate_new_constr_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_22 : generate_new_constr_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_23 : generate_new_constr_safety_wit_23.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_26 : generate_new_constr_safety_wit_26.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_27 : generate_new_constr_safety_wit_27.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_28 : generate_new_constr_safety_wit_28.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_29 : generate_new_constr_safety_wit_29.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_safety_wit_30 : generate_new_constr_safety_wit_30.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_entail_wit_1 : generate_new_constr_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_return_wit_2 : generate_new_constr_return_wit_2.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_return_wit_3 : generate_new_constr_return_wit_3.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_return_wit_4 : generate_new_constr_return_wit_4.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_return_wit_5 : generate_new_constr_return_wit_5.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_return_wit_6 : generate_new_constr_return_wit_6.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_1 : generate_new_constr_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_2 : generate_new_constr_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_3_pure : generate_new_constr_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_3 : generate_new_constr_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_4 : generate_new_constr_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_5 : generate_new_constr_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_6 : generate_new_constr_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_7 : generate_new_constr_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_8 : generate_new_constr_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_9 : generate_new_constr_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_10 : generate_new_constr_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_11 : generate_new_constr_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_12 : generate_new_constr_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_generate_new_constr_partial_solve_wit_13 : generate_new_constr_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_1 : generate_new_constraint_list_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_2 : generate_new_constraint_list_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_3 : generate_new_constraint_list_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_4 : generate_new_constraint_list_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_5 : generate_new_constraint_list_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_6 : generate_new_constraint_list_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_safety_wit_7 : generate_new_constraint_list_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_1_pure : generate_new_constraint_list_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_1 : generate_new_constraint_list_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_2_pure : generate_new_constraint_list_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_2 : generate_new_constraint_list_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_3 : generate_new_constraint_list_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_4 : generate_new_constraint_list_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_5_pure : generate_new_constraint_list_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_5 : generate_new_constraint_list_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_which_implies_wit_1 : generate_new_constraint_list_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_generate_new_constraint_list_which_implies_wit_2 : generate_new_constraint_list_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_1 : real_shadow_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_2 : real_shadow_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_3 : real_shadow_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_4 : real_shadow_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_5 : real_shadow_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_6 : real_shadow_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_7 : real_shadow_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_8 : real_shadow_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_9 : real_shadow_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_10 : real_shadow_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_11 : real_shadow_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_12 : real_shadow_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_13 : real_shadow_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_14 : real_shadow_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_15 : real_shadow_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_16 : real_shadow_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_17 : real_shadow_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_18 : real_shadow_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_19 : real_shadow_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_20 : real_shadow_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_21 : real_shadow_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_22 : real_shadow_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_23 : real_shadow_safety_wit_23.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_24 : real_shadow_safety_wit_24.
Proof. Admitted. 

Lemma proof_of_real_shadow_safety_wit_25 : real_shadow_safety_wit_25.
Proof. Admitted. 

Lemma proof_of_real_shadow_return_wit_2 : real_shadow_return_wit_2.
Proof. Admitted. 

Lemma proof_of_real_shadow_return_wit_4 : real_shadow_return_wit_4.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_1_pure : real_shadow_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_1 : real_shadow_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_2 : real_shadow_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_3 : real_shadow_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_4_pure : real_shadow_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_4 : real_shadow_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_5_pure : real_shadow_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_5 : real_shadow_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_6 : real_shadow_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_7 : real_shadow_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_8 : real_shadow_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_9 : real_shadow_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_10 : real_shadow_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_11 : real_shadow_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_12 : real_shadow_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_real_shadow_partial_solve_wit_13 : real_shadow_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_1 : lia_deduction_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_2 : lia_deduction_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_3 : lia_deduction_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_4 : lia_deduction_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_5 : lia_deduction_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_6 : lia_deduction_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_7 : lia_deduction_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_8 : lia_deduction_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_9 : lia_deduction_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_10 : lia_deduction_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_11 : lia_deduction_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_12 : lia_deduction_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_lia_deduction_safety_wit_13 : lia_deduction_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_lia_deduction_return_wit_3 : lia_deduction_return_wit_3.
Proof. Admitted. 

Lemma proof_of_lia_deduction_return_wit_4 : lia_deduction_return_wit_4.
Proof. Admitted. 

Lemma proof_of_lia_deduction_partial_solve_wit_1_pure : lia_deduction_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_lia_deduction_partial_solve_wit_1 : lia_deduction_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_lia_deduction_partial_solve_wit_2 : lia_deduction_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_lia_deduction_partial_solve_wit_3 : lia_deduction_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_lia_deduction_partial_solve_wit_4 : lia_deduction_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_lia_deduction_partial_solve_wit_5 : lia_deduction_partial_solve_wit_5.
Proof. Admitted. 

