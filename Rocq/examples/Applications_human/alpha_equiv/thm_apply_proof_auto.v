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
From SimpleC.EE.Applications_human.alpha_equiv Require Import thm_apply_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import ast_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_sub_thm_safety_wit_1 : sub_thm_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_sub_thm_safety_wit_2 : sub_thm_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_sub_thm_safety_wit_3 : sub_thm_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_1_pure : sub_thm_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_1 : sub_thm_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_2_pure : sub_thm_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_2 : sub_thm_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_3 : sub_thm_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_4 : sub_thm_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_1 : separate_imply_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_2 : separate_imply_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_3 : separate_imply_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_4 : separate_imply_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_5 : separate_imply_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_6 : separate_imply_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_7 : separate_imply_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_separate_imply_safety_wit_8 : separate_imply_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_1 : separate_imply_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_2_pure : separate_imply_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_2 : separate_imply_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_3 : separate_imply_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_4_pure : separate_imply_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_4 : separate_imply_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_5 : separate_imply_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_6_pure : separate_imply_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_6 : separate_imply_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_separate_imply_partial_solve_wit_7 : separate_imply_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_check_list_gen_safety_wit_1 : check_list_gen_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_check_list_gen_safety_wit_2 : check_list_gen_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_safety_wit_3 : check_list_gen_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_check_list_gen_safety_wit_4 : check_list_gen_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_1 : check_list_gen_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_2 : check_list_gen_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_3 : check_list_gen_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_4 : check_list_gen_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_5 : check_list_gen_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_6 : check_list_gen_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_7_pure : check_list_gen_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_7 : check_list_gen_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_8_pure : check_list_gen_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_8 : check_list_gen_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_9 : check_list_gen_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_10 : check_list_gen_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_check_list_gen_partial_solve_wit_11 : check_list_gen_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_thm_apply_safety_wit_1 : thm_apply_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_thm_apply_safety_wit_2 : thm_apply_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_thm_apply_safety_wit_3 : thm_apply_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_thm_apply_safety_wit_4 : thm_apply_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_thm_apply_safety_wit_5 : thm_apply_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_thm_apply_safety_wit_6 : thm_apply_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_1 : thm_apply_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_2 : thm_apply_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_3 : thm_apply_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_4_pure : thm_apply_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_4 : thm_apply_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_5 : thm_apply_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_6_pure : thm_apply_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_6 : thm_apply_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_7 : thm_apply_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_8_pure : thm_apply_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_8 : thm_apply_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_9_pure : thm_apply_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_thm_apply_partial_solve_wit_9 : thm_apply_partial_solve_wit_9.
Proof. Admitted. 

