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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import copy_vector_to_col_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import copy_vector_to_col_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_copy_vector_to_col_gmp_entail_wit_1_split_goal_1 :
  copy_vector_to_col_gmp_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply partial_rep_matrix_col_copy_init; [assumption | lia].
Qed.

Lemma proof_of_copy_vector_to_col_gmp_entail_wit_1 :
  copy_vector_to_col_gmp_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copy_vector_to_col_gmp_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_entail_wit_2 : copy_vector_to_col_gmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcopy :
    partial_rep_matrix_col_copy
      (replace_Znth (i * n_pre + col_pre)
        (Znth i lx_low_level_spec 0) linv_cur_2)
      n_pre col_pre (i + 1) B_low_level_spec X_low_level_spec).
  {
    replace (i * n_pre + col_pre) with
      (row_major_index n_pre i col_pre)
      by (unfold row_major_index; lia).
    eapply partial_rep_matrix_col_copy_update_next; eauto; try lia.
    eapply (rep_vector_nth lx_low_level_spec n_pre X_low_level_spec i);
      eauto; lia.
  }
  destruct (Z.eq_dec (i + 1) n_pre) as [Hdone | Hnot_done].
  - Right.
    Exists (replace_Znth (i * n_pre + col_pre)
      (Znth i lx_low_level_spec 0) linv_cur_2).
    repeat split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
  - Left. Left. Right.
    Exists (replace_Znth (i * n_pre + col_pre)
      (Znth i lx_low_level_spec 0) linv_cur_2).
    repeat split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try nia.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_1_split_goal_1 :
  copy_vector_to_col_gmp_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply partial_rep_matrix_col_copy_finish.
  replace i with n_pre in * by lia.
  assumption.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_1 :
  copy_vector_to_col_gmp_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copy_vector_to_col_gmp_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_2_split_goal_1 :
  copy_vector_to_col_gmp_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply partial_rep_matrix_col_copy_finish.
  replace i with n_pre in * by lia.
  assumption.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_2 :
  copy_vector_to_col_gmp_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copy_vector_to_col_gmp_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_3_split_goal_1 :
  copy_vector_to_col_gmp_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace i with n_pre in * by lia.
  apply partial_rep_matrix_col_copy_finish; assumption.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_3 :
  copy_vector_to_col_gmp_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copy_vector_to_col_gmp_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_4_split_goal_1 :
  copy_vector_to_col_gmp_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace i with n_pre in * by lia.
  apply partial_rep_matrix_col_copy_finish; assumption.
Qed.

Lemma proof_of_copy_vector_to_col_gmp_return_wit_4 :
  copy_vector_to_col_gmp_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copy_vector_to_col_gmp_return_wit_4_split_goal_1.
Qed.
