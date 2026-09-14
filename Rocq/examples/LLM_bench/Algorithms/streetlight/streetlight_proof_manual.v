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
From SimpleC.EE.LLM_bench.Algorithms.streetlight Require Import streetlight_goal.
From SimpleC.EE.LLM_bench.Algorithms.streetlight Require Import streetlight_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.streetlight.streetlight_lib.
Local Open Scope sac.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single pre_pre 0 0).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full pos_pre n_pre pos_l).
    cancel (IntArray.full power_pre n_pre power_l).
    cancel (IntArray.seg pre_pre 0 1 (0 :: nil)).
    cancel (IntArray.undef_seg pre_pre 1 (n_pre + 1)).
    cancel (IntArray2.full dp_l_pre n_pre n_pre dp_l_init).
    cancel (IntArray2.full dp_r_pre n_pre n_pre dp_r_init).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia;
              try (simpl; reflexivity)).
    + apply streetlight_prefix_zero_bounds__prefix_setup.
    + apply streetlight_prefix_zero_progress__prefix_setup.
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_1 : solve_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  eapply streetlight_prefix_extend__prefix_setup; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_2 : solve_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_3 : solve_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_4 : solve_entail_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_5 : solve_entail_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_6 : solve_entail_wit_3_split_goal_6.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_7 : solve_entail_wit_3_split_goal_7.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_8 : solve_entail_wit_3_split_goal_8.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3_split_goal_9 : solve_entail_wit_3_split_goal_9.
Proof. Abort.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) as Hi by lia.
  subst i.
  assert (Htable_shape :
    forall base table,
      IntArray2.full base n_pre n_pre table |--
        “ StreetlightTableShape table n_pre ”).
  {
    intros base table.
    unfold derivable1, coq_prop.
    intros state Hfull.
    apply streetlight_table_shape_from_full__prefix_setup.
    - exact
        (derivable1_imp
          (IntArray2.full base n_pre n_pre table)
          (“ Zlength table = n_pre ”)
          state
          (IntArray2.full_Zlength base n_pre n_pre table)
          Hfull).
    - intros row Hrow.
      pose proof
        (derivable1_imp
          (IntArray2.full base n_pre n_pre table)
          (IntArray2.ElemArray.full
             (IntArray2.row_addr base n_pre row)
             n_pre (Znth row table nil) **
           IntArray2.missing_i base row 0 n_pre n_pre table)
          state
          (IntArray2.full_split_to_missing_i
             base row n_pre n_pre table Hrow)
          Hfull) as Hsplit.
      unfold sepcon in Hsplit.
      destruct Hsplit as
        (row_state & rest_state & Hjoin & Hrowfull & Hrest).
      exact
        (derivable1_imp
          (IntArray2.ElemArray.full
             (IntArray2.row_addr base n_pre row)
             n_pre (Znth row table nil))
          (“ Zlength (Znth row table nil) = n_pre ”)
          row_state
          (IntArray2.ElemArray.full_Zlength
             (IntArray2.row_addr base n_pre row)
             n_pre (Znth row table nil))
          Hrowfull).
  }
  prop_apply (Htable_shape dp_l_pre dp_l_init).
  Intros_p Hleft_shape.
  prop_apply (Htable_shape dp_r_pre dp_r_init).
  Intros_p Hright_shape.
  assert (Hprefix_positive : 1 <= Znth n_pre prefix_l 0).
  {
    eapply streetlight_prefix_total_positive__prefix_setup.
    - exact PreH4.
    - exact PreH11.
    - intros k Hk.
      specialize (PreH14 k Hk).
      lia.
    - exact PreH16.
  }
  assert (Hprefix_bounds : 0 <= Znth n_pre prefix_l 0 <= 5000).
  {
    apply PreH15.
    lia.
  }
  replace (n_pre - 0) with n_pre by lia.
  Exists dp_r_init dp_l_init prefix_l.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.seg_to_full pre_pre 0 (n_pre + 1) prefix_l).
    replace (pre_pre + 0 * sizeof (INT)) with pre_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel (IntArray.full pos_pre n_pre pos_l).
    cancel (IntArray.full power_pre n_pre power_l).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l).
    cancel (IntArray2.full dp_l_pre n_pre n_pre dp_l_init).
    cancel (IntArray2.full dp_r_pre n_pre n_pre dp_r_init).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia;
              try (simpl; reflexivity)).
    + apply streetlight_inf_rows_zero__prefix_setup.
      exact Hleft_shape.
    + apply streetlight_inf_rows_zero__prefix_setup.
      exact Hright_shape.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightInfProgress.
  split.
  - exact PreH21.
  - intros col Hcol.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightInfProgress.
  split.
  - exact PreH20.
  - intros col Hcol.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_3 : solve_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH18.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_4 : solve_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH17.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_5 : solve_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_6 : solve_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH15.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_6.
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst inf.
  Exists
    (replace_Znth row
      (replace_Znth col 2147483647
        (Znth row right_table_2 __default__List_Z))
      right_table_2)
    (replace_Znth row
      (replace_Znth col 2147483647
        (Znth row left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    eapply streetlight_inf_progress_store__inf_tables;
    eauto;
    lia
  ].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_r_pre + row * n_pre * sizeof (INT)) col n_pre 2147483647
    (Znth row right_table_2 __default__List_Z) ltac:(lia))
    as Hright_row_merge.
  simpl in Hright_row_merge.
  assert (Hright_addr :
    dp_r_pre + row * n_pre * sizeof (INT) + col * sizeof (INT) =
    dp_r_pre + (row * n_pre + col) * sizeof (INT)) by lia.
  rewrite <- Hright_addr.
  sep_apply Hright_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_r_pre row n_pre n_pre right_table_2
    (replace_Znth col 2147483647
      (Znth row right_table_2 __default__List_Z)) ltac:(lia))
    as Hright_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre row) n_pre
      (replace_Znth col 2147483647
        (Znth row right_table_2 __default__List_Z)))
    with
    (IntArray.full
      (dp_r_pre + row * n_pre * 4) n_pre
      (replace_Znth col 2147483647
        (Znth row right_table_2 __default__List_Z)))
    in Hright_table_merge.
  sep_apply Hright_table_merge.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_l_pre + row * n_pre * sizeof (INT)) col n_pre 2147483647
    (Znth row left_table_2 __default__List_Z) ltac:(lia))
    as Hleft_row_merge.
  simpl in Hleft_row_merge.
  assert (Hleft_addr :
    dp_l_pre + row * n_pre * sizeof (INT) + col * sizeof (INT) =
    dp_l_pre + (row * n_pre + col) * sizeof (INT)) by lia.
  rewrite <- Hleft_addr.
  rewrite sizeof_int.
  sep_apply Hleft_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_l_pre row n_pre n_pre left_table_2
    (replace_Znth col 2147483647
      (Znth row left_table_2 __default__List_Z)) ltac:(lia))
    as Hleft_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre row) n_pre
      (replace_Znth col 2147483647
        (Znth row left_table_2 __default__List_Z)))
    with
    (IntArray.full
      (dp_l_pre + row * n_pre * 4) n_pre
      (replace_Znth col 2147483647
        (Znth row left_table_2 __default__List_Z)))
    in Hleft_table_merge.
  sep_apply Hleft_table_merge.
  cancel.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_1 : solve_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (streetlight_inf_progress_close_row__inf_tables
    right_table_2 n_pre row col).
  - lia.
  - exact PreH23.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_2 : solve_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (streetlight_inf_progress_close_row__inf_tables
    left_table_2 n_pre row col).
  - lia.
  - exact PreH22.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_3 : solve_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH20.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_4 : solve_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH19.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_5 : solve_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_6 : solve_entail_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH17.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_6.
Qed.

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hrow : row = n_pre) by lia.
  subst row.
  subst inf.
  pose proof
    (streetlight_diagonal_base__diagonal_base
      pos_l power_l left_table_2 right_table_2 n_pre start
      __default__List_Z ltac:(lia) PreH20 PreH21)
    as [Hlengths [Hpending_right Hpending_left]].
  Exists
    (replace_Znth start
      (replace_Znth start 0
        (Znth start right_table_2 __default__List_Z))
      right_table_2)
    (replace_Znth start
      (replace_Znth start 0
        (Znth start left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    intros pending Hpending;
    apply Hpending_right;
    lia
  ].
  all: try solve [
    dump_pre_spatial;
    intros pending Hpending;
    apply Hpending_left;
    lia
  ].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_r_pre + start * n_pre * sizeof (INT)) start n_pre 0
    (Znth start right_table_2 __default__List_Z) ltac:(lia))
    as Hright_row_merge.
  simpl in Hright_row_merge.
  assert (Hright_addr :
    dp_r_pre + start * n_pre * sizeof (INT) + start * sizeof (INT) =
    dp_r_pre + (start * n_pre + start) * sizeof (INT)) by lia.
  rewrite <- Hright_addr.
  sep_apply Hright_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_r_pre start n_pre n_pre right_table_2
    (replace_Znth start 0
      (Znth start right_table_2 __default__List_Z)) ltac:(lia))
    as Hright_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre start) n_pre
      (replace_Znth start 0
        (Znth start right_table_2 __default__List_Z)))
    with
    (IntArray.full
      (dp_r_pre + start * n_pre * 4) n_pre
      (replace_Znth start 0
        (Znth start right_table_2 __default__List_Z)))
    in Hright_table_merge.
  sep_apply Hright_table_merge.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_l_pre + start * n_pre * sizeof (INT)) start n_pre 0
    (Znth start left_table_2 __default__List_Z) ltac:(lia))
    as Hleft_row_merge.
  simpl in Hleft_row_merge.
  assert (Hleft_addr :
    dp_l_pre + start * n_pre * sizeof (INT) + start * sizeof (INT) =
    dp_l_pre + (start * n_pre + start) * sizeof (INT)) by lia.
  rewrite <- Hleft_addr.
  rewrite sizeof_int.
  sep_apply Hleft_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_l_pre start n_pre n_pre left_table_2
    (replace_Znth start 0
      (Znth start left_table_2 __default__List_Z)) ltac:(lia))
    as Hleft_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre start) n_pre
      (replace_Znth start 0
        (Znth start left_table_2 __default__List_Z)))
    with
    (IntArray.full
      (dp_l_pre + start * n_pre * 4) n_pre
      (replace_Znth start 0
        (Znth start left_table_2 __default__List_Z)))
    in Hleft_table_merge.
  sep_apply Hleft_table_merge.
  cancel.
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_1 : solve_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
    eauto using streetlight_left_progress_zero__length_entry.
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_2 : solve_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); exact PreH24.
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_3 : solve_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); exact PreH23.
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_4 : solve_entail_wit_8_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH22 k_4 H).
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_5 : solve_entail_wit_8_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH21 k_3 H).
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_6 : solve_entail_wit_8_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_8_1_split_goal_7 : solve_entail_wit_8_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH19 k H).
Qed.

Lemma proof_of_solve_entail_wit_8_1 : solve_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_8_1_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_8_2 : solve_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_left_progress_initial__length_entry
       pos_l power_l left_table_2 right_table_2 n_pre start len PreH26)
    as Hprogress.
  Left.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_l).
    cancel (IntArray.full power_pre n_pre power_l).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
    cancel (IntArray2.full dp_l_pre n_pre n_pre left_table_2).
    cancel (IntArray2.full dp_r_pre n_pre n_pre right_table_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: lia.
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_1 : solve_entail_wit_8_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
    eauto using streetlight_left_progress_zero__length_entry.
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_2 : solve_entail_wit_8_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); exact PreH24.
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_3 : solve_entail_wit_8_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); exact PreH23.
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_4 : solve_entail_wit_8_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH22 k_4 H).
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_5 : solve_entail_wit_8_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH21 k_3 H).
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_6 : solve_entail_wit_8_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_8_3_split_goal_7 : solve_entail_wit_8_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH19 k H).
Qed.

Lemma proof_of_solve_entail_wit_8_3 : solve_entail_wit_8_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_8_3_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_8_4 : solve_entail_wit_8_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_left_progress_initial__length_entry
       pos_l power_l left_table_2 right_table_2 n_pre start len PreH26)
    as Hprogress.
  Left.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_l).
    cancel (IntArray.full power_pre n_pre power_l).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
    cancel (IntArray2.full dp_l_pre n_pre n_pre left_table_2).
    cancel (IntArray2.full dp_r_pre n_pre n_pre right_table_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: lia.
Qed.

Lemma proof_of_solve_entail_wit_10_1 : solve_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (streetlight_remaining_bounds__left_remain
    power_l prefix_l n_pre total left (left + len - 1)
    PreH41 PreH44 PreH48 PreH21 PreH2 ltac:(lia) PreH5) as Hremain.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_10_2 : solve_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (streetlight_remaining_bounds__left_remain
    power_l prefix_l_2 n_pre total left (left + len - 1)
    PreH41 PreH44 PreH48 PreH21 PreH2 ltac:(lia) PreH5) as Hremain.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_10_3 : solve_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (streetlight_remaining_bounds__left_remain
    power_l prefix_l_3 n_pre total left (left + len - 1)
    PreH41 PreH44 PreH48 PreH21 PreH2 ltac:(lia) PreH5) as Hremain.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_10_4 : solve_entail_wit_10_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (streetlight_remaining_bounds__left_remain
    power_l prefix_l_4 n_pre total left (left + len - 1)
    PreH41 PreH44 PreH48 PreH21 PreH2 ltac:(lia) PreH5) as Hremain.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_11_1 : solve_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_previous_left_entry_bounds__left_predecessor
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre total start len left inf
       PreH43 PreH44 PreH24 PreH34 PreH45 PreH46 PreH47
       PreH5 PreH4 PreH7 PreH8 PreH31 PreH22 PreH51 PreH52 PreH1)
    as Hprevious_bounds.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_11_2 : solve_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_previous_left_entry_bounds__left_predecessor
       pos_l power_l prefix_l_2 left_table_2 right_table_2 __default__List_Z
       n_pre total start len left inf
       PreH43 PreH44 PreH24 PreH34 PreH45 PreH46 PreH47
       PreH5 PreH4 PreH7 PreH8 PreH31 PreH22 PreH51 PreH52 PreH1)
    as Hprevious_bounds.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_11_3 : solve_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_previous_left_entry_bounds__left_predecessor
       pos_l power_l prefix_l_3 left_table_3 right_table_3 __default__List_Z
       n_pre total start len left inf
       PreH43 PreH44 PreH24 PreH34 PreH45 PreH46 PreH47
       PreH5 PreH4 PreH7 PreH8 PreH31 PreH22 PreH51 PreH52 PreH1)
    as Hprevious_bounds.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_11_4 : solve_entail_wit_11_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_previous_left_entry_bounds__left_predecessor
       pos_l power_l prefix_l_4 left_table_4 right_table_4 __default__List_Z
       n_pre total start len left inf
       PreH43 PreH44 PreH24 PreH34 PreH45 PreH46 PreH47
       PreH5 PreH4 PreH7 PreH8 PreH31 PreH22 PreH51 PreH52 PreH1)
    as Hprevious_bounds.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_12_1 : solve_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpos_left : 0 <= Znth left pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_next : 0 <= Znth (left + 1) pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_step : Znth left pos_l 0 < Znth (left + 1) pos_l 0) by
    (apply PreH48; lia).
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      first [assumption | nia].
Qed.

Lemma proof_of_solve_entail_wit_12_2 : solve_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpos_left : 0 <= Znth left pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_next : 0 <= Znth (left + 1) pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_step : Znth left pos_l 0 < Znth (left + 1) pos_l 0) by
    (apply PreH48; lia).
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      first [assumption | nia].
Qed.

Lemma proof_of_solve_entail_wit_12_3 : solve_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpos_left : 0 <= Znth left pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_next : 0 <= Znth (left + 1) pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_step : Znth left pos_l 0 < Znth (left + 1) pos_l 0) by
    (apply PreH48; lia).
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      first [assumption | nia].
Qed.

Lemma proof_of_solve_entail_wit_12_4 : solve_entail_wit_12_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpos_left : 0 <= Znth left pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_next : 0 <= Znth (left + 1) pos_l 0 <= 8000) by
    (apply PreH47; lia).
  assert (Hpos_step : Znth left pos_l 0 < Znth (left + 1) pos_l 0) by
    (apply PreH48; lia).
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      first [assumption | nia].
Qed.

Lemma proof_of_solve_entail_wit_13_1 : solve_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__left_best_a
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left total inf
       PreH48 PreH49 PreH50 PreH51 PreH52
       PreH29 PreH39 PreH56 PreH57
       PreH10 PreH9 PreH12 PreH13 PreH27 PreH1)
    as Hrightbounds.
  destruct Hrightbounds as [Hrightnonneg Hrightupper].
  Left.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solve_entail_wit_13_2 : solve_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__left_best_a
       pos_l power_l prefix_l_2 left_table_2 right_table_2 __default__List_Z
       n_pre start len left total inf
       PreH48 PreH49 PreH50 PreH51 PreH52
       PreH29 PreH39 PreH56 PreH57
       PreH10 PreH9 PreH12 PreH13 PreH27 PreH1)
    as Hrightbounds.
  destruct Hrightbounds as [Hrightnonneg Hrightupper].
  Left.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solve_entail_wit_13_3 : solve_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__left_best_a
       pos_l power_l prefix_l_3 left_table_3 right_table_3 __default__List_Z
       n_pre start len left total inf
       PreH48 PreH49 PreH50 PreH51 PreH52
       PreH29 PreH39 PreH56 PreH57
       PreH10 PreH9 PreH12 PreH13 PreH27 PreH1)
    as Hrightbounds.
  destruct Hrightbounds as [Hrightnonneg Hrightupper].
  Left.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solve_entail_wit_13_4 : solve_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__left_best_a
       pos_l power_l prefix_l_4 left_table_4 right_table_4 __default__List_Z
       n_pre start len left total inf
       PreH48 PreH49 PreH50 PreH51 PreH52
       PreH29 PreH39 PreH56 PreH57
       PreH10 PreH9 PreH12 PreH13 PreH27 PreH1)
    as Hrightbounds.
  destruct Hrightbounds as [Hrightnonneg Hrightupper].
  Left.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solve_entail_wit_13_5 : solve_entail_wit_13_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightLeftProgress_predecessor_right_bounds__left_best_b
      pos_l power_l left_table right_table n_pre start len left
      __default__List_Z PreH44 PreH45 PreH27 PreH32 PreH6 PreH5
      PreH8 PreH9 PreH46 PreH47 PreH48 PreH53 ltac:(lia))
    as Hprev_bounds.
  Left.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_13_6 : solve_entail_wit_13_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightLeftProgress_predecessor_right_bounds__left_best_b
      pos_l power_l left_table_2 right_table_2 n_pre start len left
      __default__List_Z PreH44 PreH45 PreH27 PreH32 PreH6 PreH5
      PreH8 PreH9 PreH46 PreH47 PreH48 PreH53 ltac:(lia))
    as Hprev_bounds.
  Left.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_13_7 : solve_entail_wit_13_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightLeftProgress_predecessor_right_bounds__left_best_b
      pos_l power_l left_table_3 right_table_3 n_pre start len left
      __default__List_Z PreH44 PreH45 PreH27 PreH32 PreH6 PreH5
      PreH8 PreH9 PreH46 PreH47 PreH48 PreH53 ltac:(lia))
    as Hprev_bounds.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_13_8 : solve_entail_wit_13_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightLeftProgress_predecessor_right_bounds__left_best_b
      pos_l power_l left_table_4 right_table_4 n_pre start len left
      __default__List_Z PreH44 PreH45 PreH27 PreH32 PreH6 PreH5
      PreH8 PreH9 PreH46 PreH47 PreH48 PreH53 ltac:(lia))
    as Hprev_bounds.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_14_1 : solve_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 left ltac:(lia)) as Hpos_left.
  pose proof (PreH52 (left + len - 1) ltac:(lia)) as Hpos_right.
  pose proof
    (streetlight_adjacent_positions_strict__left_compare_a
       pos_l n_pre PreH53 left (left + len - 1)
       PreH12 ltac:(lia) PreH15) as Hpos_order.
  assert (Hcandidate_bounds :
    0 <=
      Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0)) /\
    Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0)) <=
      (len - 1) * 40000000).
  {
    eapply streetlight_left_candidate_bounds__left_compare_a.
    - exact PreH1.
    - exact PreH2.
    - lia.
    - exact (proj1 Hpos_left).
    - exact (proj2 Hpos_right).
    - exact PreH9.
    - exact PreH10.
  }
  destruct Hcandidate_bounds as [Hcandidate_lower Hcandidate_upper].
  Left.
  Left.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_l).
    cancel ((( &( "cand" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0 +
       (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0)))).
    cancel ((( &( "prev" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0)).
    cancel (((dp_r_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_r_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) right_table __default__List_Z)).
    cancel (IntArray2.missing_i dp_r_pre (left + 1) 0 n_pre n_pre right_table).
    cancel ((( &( "best" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table __default__List_Z) 0 +
       (Znth (left + 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0)))).
    cancel (((dp_l_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_l_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) left_table __default__List_Z)).
    cancel (IntArray2.missing_i dp_l_pre (left + 1) 0 n_pre n_pre left_table).
    cancel ((( &( "remain" ) )) # Int |->
      (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0))).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l).
    cancel ((( &( "right" ) )) # Int |-> (left + len - 1)).
    cancel (IntArray.full power_pre n_pre power_l).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_14_2 : solve_entail_wit_14_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 left ltac:(lia)) as Hpos_left.
  pose proof (PreH52 (left + len - 1) ltac:(lia)) as Hpos_right.
  pose proof
    (streetlight_adjacent_positions_strict__left_compare_a
       pos_l n_pre PreH53 left (left + len - 1)
       PreH12 ltac:(lia) PreH15) as Hpos_order.
  assert (Hcandidate_bounds :
    0 <=
      Znth (left + len - 1) (Znth (left + 1) right_table_2 __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l_2 0 - Znth (left + 1) prefix_l_2 0)) /\
    Znth (left + len - 1) (Znth (left + 1) right_table_2 __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l_2 0 - Znth (left + 1) prefix_l_2 0)) <=
      (len - 1) * 40000000).
  {
    eapply streetlight_left_candidate_bounds__left_compare_a.
    - exact PreH1.
    - exact PreH2.
    - lia.
    - exact (proj1 Hpos_left).
    - exact (proj2 Hpos_right).
    - exact PreH9.
    - exact PreH10.
  }
  destruct Hcandidate_bounds as [Hcandidate_lower Hcandidate_upper].
  Left.
  Left.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_l).
    cancel ((( &( "cand" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_2 __default__List_Z) 0 +
       (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l_2 0 - Znth (left + 1) prefix_l_2 0)))).
    cancel ((( &( "prev" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_2 __default__List_Z) 0)).
    cancel (((dp_r_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_2 __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_r_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) right_table_2 __default__List_Z)).
    cancel (IntArray2.missing_i dp_r_pre (left + 1) 0 n_pre n_pre right_table_2).
    cancel ((( &( "best" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table_2 __default__List_Z) 0 +
       (Znth (left + 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l_2 0 - Znth (left + 1) prefix_l_2 0)))).
    cancel (((dp_l_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table_2 __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_l_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) left_table_2 __default__List_Z)).
    cancel (IntArray2.missing_i dp_l_pre (left + 1) 0 n_pre n_pre left_table_2).
    cancel ((( &( "remain" ) )) # Int |->
      (total - (Znth (left + len - 1 + 1) prefix_l_2 0 - Znth (left + 1) prefix_l_2 0))).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
    cancel ((( &( "right" ) )) # Int |-> (left + len - 1)).
    cancel (IntArray.full power_pre n_pre power_l).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_14_3 : solve_entail_wit_14_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 left ltac:(lia)) as Hpos_left.
  pose proof (PreH52 (left + len - 1) ltac:(lia)) as Hpos_right.
  pose proof
    (streetlight_adjacent_positions_strict__left_compare_a
       pos_l n_pre PreH53 left (left + len - 1)
       PreH12 ltac:(lia) PreH15) as Hpos_order.
  assert (Hcandidate_bounds :
    0 <=
      Znth (left + len - 1) (Znth (left + 1) right_table_3 __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l_3 0 - Znth (left + 1) prefix_l_3 0)) /\
    Znth (left + len - 1) (Znth (left + 1) right_table_3 __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l_3 0 - Znth (left + 1) prefix_l_3 0)) <=
      (len - 1) * 40000000).
  {
    eapply streetlight_left_candidate_bounds__left_compare_a.
    - exact PreH1.
    - exact PreH2.
    - lia.
    - exact (proj1 Hpos_left).
    - exact (proj2 Hpos_right).
    - exact PreH9.
    - exact PreH10.
  }
  destruct Hcandidate_bounds as [Hcandidate_lower Hcandidate_upper].
  Left.
  Right.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_l).
    cancel ((( &( "cand" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_3 __default__List_Z) 0 +
       (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l_3 0 - Znth (left + 1) prefix_l_3 0)))).
    cancel ((( &( "prev" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_3 __default__List_Z) 0)).
    cancel (((dp_r_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_3 __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_r_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) right_table_3 __default__List_Z)).
    cancel (IntArray2.missing_i dp_r_pre (left + 1) 0 n_pre n_pre right_table_3).
    cancel ((( &( "best" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table_3 __default__List_Z) 0 +
       (Znth (left + 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l_3 0 - Znth (left + 1) prefix_l_3 0)))).
    cancel (((dp_l_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table_3 __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_l_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) left_table_3 __default__List_Z)).
    cancel (IntArray2.missing_i dp_l_pre (left + 1) 0 n_pre n_pre left_table_3).
    cancel ((( &( "remain" ) )) # Int |->
      (total - (Znth (left + len - 1 + 1) prefix_l_3 0 - Znth (left + 1) prefix_l_3 0))).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_3).
    cancel ((( &( "right" ) )) # Int |-> (left + len - 1)).
    cancel (IntArray.full power_pre n_pre power_l).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_14_4 : solve_entail_wit_14_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 left ltac:(lia)) as Hpos_left.
  pose proof (PreH52 (left + len - 1) ltac:(lia)) as Hpos_right.
  pose proof
    (streetlight_adjacent_positions_strict__left_compare_a
       pos_l n_pre PreH53 left (left + len - 1)
       PreH12 ltac:(lia) PreH15) as Hpos_order.
  assert (Hcandidate_bounds :
    0 <=
      Znth (left + len - 1) (Znth (left + 1) right_table_4 __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l_4 0 - Znth (left + 1) prefix_l_4 0)) /\
    Znth (left + len - 1) (Znth (left + 1) right_table_4 __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l_4 0 - Znth (left + 1) prefix_l_4 0)) <=
      (len - 1) * 40000000).
  {
    eapply streetlight_left_candidate_bounds__left_compare_a.
    - exact PreH1.
    - exact PreH2.
    - lia.
    - exact (proj1 Hpos_left).
    - exact (proj2 Hpos_right).
    - exact PreH9.
    - exact PreH10.
  }
  destruct Hcandidate_bounds as [Hcandidate_lower Hcandidate_upper].
  Left.
  Right.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_l).
    cancel ((( &( "cand" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_4 __default__List_Z) 0 +
       (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l_4 0 - Znth (left + 1) prefix_l_4 0)))).
    cancel ((( &( "prev" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_4 __default__List_Z) 0)).
    cancel (((dp_r_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) right_table_4 __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_r_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) right_table_4 __default__List_Z)).
    cancel (IntArray2.missing_i dp_r_pre (left + 1) 0 n_pre n_pre right_table_4).
    cancel ((( &( "best" ) )) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table_4 __default__List_Z) 0 +
       (Znth (left + 1) pos_l 0 - Znth left pos_l 0) *
       (total - (Znth (left + len - 1 + 1) prefix_l_4 0 - Znth (left + 1) prefix_l_4 0)))).
    cancel (((dp_l_pre + ((((left + 1) * n_pre) + ((left + len) - 1)) * sizeof(INT)))) # Int |->
      (Znth (left + len - 1) (Znth (left + 1) left_table_4 __default__List_Z) 0)).
    cancel (IntArray.missing_i (dp_l_pre + (((left + 1) * n_pre) * sizeof(INT))) ((left + len) - 1) 0 n_pre (Znth (left + 1) left_table_4 __default__List_Z)).
    cancel (IntArray2.missing_i dp_l_pre (left + 1) 0 n_pre n_pre left_table_4).
    cancel ((( &( "remain" ) )) # Int |->
      (total - (Znth (left + len - 1 + 1) prefix_l_4 0 - Znth (left + 1) prefix_l_4 0))).
    cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_4).
    cancel ((( &( "right" ) )) # Int |-> (left + len - 1)).
    cancel (IntArray.full power_pre n_pre power_l).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solve_entail_wit_14_5 : solve_entail_wit_14_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposition_order :
    Znth left pos_l 0 < Znth (left + len - 1) pos_l 0).
  { eapply streetlight_strict_positions_between__left_compare_b;
      eauto; lia. }
  pose proof (PreH48 left ltac:(lia)) as Hposition_left.
  pose proof (PreH48 (left + len - 1) ltac:(lia)) as Hposition_right.
  Left.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try nia;
      assumption.
Qed.

Lemma proof_of_solve_entail_wit_14_6 : solve_entail_wit_14_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposition_order :
    Znth left pos_l 0 < Znth (left + len - 1) pos_l 0).
  { eapply streetlight_strict_positions_between__left_compare_b;
      eauto; lia. }
  pose proof (PreH48 left ltac:(lia)) as Hposition_left.
  pose proof (PreH48 (left + len - 1) ltac:(lia)) as Hposition_right.
  Left.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try nia;
      assumption.
Qed.

Lemma proof_of_solve_entail_wit_14_7 : solve_entail_wit_14_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposition_order :
    Znth left pos_l 0 < Znth (left + len - 1) pos_l 0).
  { eapply streetlight_strict_positions_between__left_compare_b;
      eauto; lia. }
  pose proof (PreH48 left ltac:(lia)) as Hposition_left.
  pose proof (PreH48 (left + len - 1) ltac:(lia)) as Hposition_right.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try nia;
      assumption.
Qed.

Lemma proof_of_solve_entail_wit_14_8 : solve_entail_wit_14_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposition_order :
    Znth left pos_l 0 < Znth (left + len - 1) pos_l 0).
  { eapply streetlight_strict_positions_between__left_compare_b;
      eauto; lia. }
  pose proof (PreH48 left ltac:(lia)) as Hposition_left.
  pose proof (PreH48 (left + len - 1) ltac:(lia)) as Hposition_right.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try nia;
      assumption.
Qed.

Lemma proof_of_solve_entail_wit_15_1 : solve_entail_wit_15_1.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof PreH62 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Left. Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_2 : solve_entail_wit_15_2.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof PreH62 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Left. Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_3 : solve_entail_wit_15_3.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof PreH62 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_4 : solve_entail_wit_15_4.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof PreH62 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_5 : solve_entail_wit_15_5.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof PreH58 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Left. Left. Left. Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_6 : solve_entail_wit_15_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposstep :
    Znth left pos_l 0 < Znth (left + 1) pos_l 0).
  { apply PreH52. lia. }
  Left.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z)) as Hrtablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) right_table __default__List_Z))
      in Hrtablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hrrowmerge.
    assert (Hraddr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_r_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hraddr.
    sep_apply Hrrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hrtablemerge; try lia.
    rewrite replace_Znth_Znth.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hltablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) left_table_2 __default__List_Z))
      in Hltablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hlrowmerge.
    assert (Hladdr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_l_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hladdr.
    sep_apply Hlrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hltablemerge; try lia.
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_solve_entail_wit_15_7 : solve_entail_wit_15_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposstep :
    Znth left pos_l 0 < Znth (left + 1) pos_l 0).
  { apply PreH52. lia. }
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z)) as Hrtablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) right_table __default__List_Z))
      in Hrtablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hrrowmerge.
    assert (Hraddr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_r_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hraddr.
    sep_apply Hrrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hrtablemerge; try lia.
    rewrite replace_Znth_Znth.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hltablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) left_table_2 __default__List_Z))
      in Hltablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hlrowmerge.
    assert (Hladdr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_l_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hladdr.
    sep_apply Hlrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hltablemerge; try lia.
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_solve_entail_wit_15_8 : solve_entail_wit_15_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposstep :
    Znth left pos_l 0 < Znth (left + 1) pos_l 0).
  { apply PreH52. lia. }
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z)) as Hrtablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) right_table __default__List_Z))
      in Hrtablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hrrowmerge.
    assert (Hraddr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_r_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hraddr.
    sep_apply Hrrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hrtablemerge; try lia.
    rewrite replace_Znth_Znth.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hltablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) left_table_2 __default__List_Z))
      in Hltablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hlrowmerge.
    assert (Hladdr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_l_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hladdr.
    sep_apply Hlrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hltablemerge; try lia.
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_solve_entail_wit_15_9 : solve_entail_wit_15_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposstep :
    Znth left pos_l 0 < Znth (left + 1) pos_l 0).
  { apply PreH56. lia. }
  repeat Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z)) as Hrtablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) right_table __default__List_Z))
      in Hrtablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hrrowmerge.
    assert (Hraddr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_r_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hraddr.
    sep_apply Hrrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hrtablemerge; try lia.
    rewrite replace_Znth_Znth.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table
      (Znth (left + 1) left_table __default__List_Z)) as Hltablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table __default__List_Z)) with
      (IntArray.full (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) left_table __default__List_Z))
      in Hltablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) left_table __default__List_Z) 0)
      (Znth (left + 1) left_table __default__List_Z)) as Hlrowmerge.
    assert (Hladdr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_l_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hladdr.
    sep_apply Hlrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hltablemerge; try lia.
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_solve_entail_wit_15_10 : solve_entail_wit_15_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hposstep :
    Znth left pos_l 0 < Znth (left + 1) pos_l 0).
  { apply PreH56. lia. }
  repeat Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_r_pre (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z)) as Hrtablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) right_table __default__List_Z))
      in Hrtablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hrrowmerge.
    assert (Hraddr :
      dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_r_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hraddr.
    sep_apply Hrrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hrtablemerge; try lia.
    rewrite replace_Znth_Znth.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre (left + 1) n_pre n_pre left_table
      (Znth (left + 1) left_table __default__List_Z)) as Hltablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table __default__List_Z)) with
      (IntArray.full (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) left_table __default__List_Z))
      in Hltablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) left_table __default__List_Z) 0)
      (Znth (left + 1) left_table __default__List_Z)) as Hlrowmerge.
    assert (Hladdr :
      dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      dp_l_pre + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hladdr.
    sep_apply Hlrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hltablemerge; try lia.
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_solve_entail_wit_15_11 : solve_entail_wit_15_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Left.
  Left.
  Left.
  Right.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
      with
      ((dp_r_pre + (left + 1) * n_pre * sizeof (INT)) +
       (left + len - 1) * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        (left + len - 1) n_pre
        (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)
        (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; lia.
    + rewrite replace_Znth_Znth by lia.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre (left + 1) n_pre n_pre right_table
          (Znth (left + 1) right_table __default__List_Z))
        as Hmerge_right.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray.full
          (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        in Hmerge_right.
      sep_apply_l_atomic Hmerge_right.
      * dump_pre_spatial; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
          with
          ((dp_l_pre + (left + 1) * n_pre * sizeof (INT)) +
           (left + len - 1) * sizeof (INT))
          by (rewrite sizeof_int; lia).
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
            (left + len - 1) n_pre
            (Znth (left + len - 1)
              (Znth (left + 1) left_table __default__List_Z) 0)
            (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial; lia.
        -- rewrite replace_Znth_Znth by lia.
           pose proof
             (IntArray2.missing_i_merge_to_full
               dp_l_pre (left + 1) n_pre n_pre left_table
               (Znth (left + 1) left_table __default__List_Z))
             as Hmerge_left.
           change
             (IntArray2.ElemArray.full
               (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray.full
               (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             in Hmerge_left.
           sep_apply_l_atomic Hmerge_left.
           ++ dump_pre_spatial; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_12 : solve_entail_wit_15_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Left.
  Left.
  Left.
  Right.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
      with
      ((dp_r_pre + (left + 1) * n_pre * sizeof (INT)) +
       (left + len - 1) * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        (left + len - 1) n_pre
        (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)
        (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; lia.
    + rewrite replace_Znth_Znth by lia.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre (left + 1) n_pre n_pre right_table
          (Znth (left + 1) right_table __default__List_Z))
        as Hmerge_right.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray.full
          (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        in Hmerge_right.
      sep_apply_l_atomic Hmerge_right.
      * dump_pre_spatial; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
          with
          ((dp_l_pre + (left + 1) * n_pre * sizeof (INT)) +
           (left + len - 1) * sizeof (INT))
          by (rewrite sizeof_int; lia).
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
            (left + len - 1) n_pre
            (Znth (left + len - 1)
              (Znth (left + 1) left_table __default__List_Z) 0)
            (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial; lia.
        -- rewrite replace_Znth_Znth by lia.
           pose proof
             (IntArray2.missing_i_merge_to_full
               dp_l_pre (left + 1) n_pre n_pre left_table
               (Znth (left + 1) left_table __default__List_Z))
             as Hmerge_left.
           change
             (IntArray2.ElemArray.full
               (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray.full
               (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             in Hmerge_left.
           sep_apply_l_atomic Hmerge_left.
           ++ dump_pre_spatial; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_13 : solve_entail_wit_15_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Left.
  Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
      with
      ((dp_r_pre + (left + 1) * n_pre * sizeof (INT)) +
       (left + len - 1) * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        (left + len - 1) n_pre
        (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)
        (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; lia.
    + rewrite replace_Znth_Znth by lia.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre (left + 1) n_pre n_pre right_table
          (Znth (left + 1) right_table __default__List_Z))
        as Hmerge_right.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray.full
          (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        in Hmerge_right.
      sep_apply_l_atomic Hmerge_right.
      * dump_pre_spatial; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
          with
          ((dp_l_pre + (left + 1) * n_pre * sizeof (INT)) +
           (left + len - 1) * sizeof (INT))
          by (rewrite sizeof_int; lia).
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
            (left + len - 1) n_pre
            (Znth (left + len - 1)
              (Znth (left + 1) left_table __default__List_Z) 0)
            (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial; lia.
        -- rewrite replace_Znth_Znth by lia.
           pose proof
             (IntArray2.missing_i_merge_to_full
               dp_l_pre (left + 1) n_pre n_pre left_table
               (Znth (left + 1) left_table __default__List_Z))
             as Hmerge_left.
           change
             (IntArray2.ElemArray.full
               (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray.full
               (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             in Hmerge_left.
           sep_apply_l_atomic Hmerge_left.
           ++ dump_pre_spatial; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_14 : solve_entail_wit_15_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Left.
  Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
      with
      ((dp_r_pre + (left + 1) * n_pre * sizeof (INT)) +
       (left + len - 1) * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        (left + len - 1) n_pre
        (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)
        (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; lia.
    + rewrite replace_Znth_Znth by lia.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre (left + 1) n_pre n_pre right_table
          (Znth (left + 1) right_table __default__List_Z))
        as Hmerge_right.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray.full
          (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        in Hmerge_right.
      sep_apply_l_atomic Hmerge_right.
      * dump_pre_spatial; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
          with
          ((dp_l_pre + (left + 1) * n_pre * sizeof (INT)) +
           (left + len - 1) * sizeof (INT))
          by (rewrite sizeof_int; lia).
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
            (left + len - 1) n_pre
            (Znth (left + len - 1)
              (Znth (left + 1) left_table __default__List_Z) 0)
            (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial; lia.
        -- rewrite replace_Znth_Znth by lia.
           pose proof
             (IntArray2.missing_i_merge_to_full
               dp_l_pre (left + 1) n_pre n_pre left_table
               (Znth (left + 1) left_table __default__List_Z))
             as Hmerge_left.
           change
             (IntArray2.ElemArray.full
               (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray.full
               (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             in Hmerge_left.
           sep_apply_l_atomic Hmerge_left.
           ++ dump_pre_spatial; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_15 : solve_entail_wit_15_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Left.
  Right.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
      with
      ((dp_r_pre + (left + 1) * n_pre * sizeof (INT)) +
       (left + len - 1) * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
        (left + len - 1) n_pre
        (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)
        (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; lia.
    + rewrite replace_Znth_Znth by lia.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre (left + 1) n_pre n_pre right_table
          (Znth (left + 1) right_table __default__List_Z))
        as Hmerge_right.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray.full
          (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        in Hmerge_right.
      sep_apply_l_atomic Hmerge_right.
      * dump_pre_spatial; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
          with
          ((dp_l_pre + (left + 1) * n_pre * sizeof (INT)) +
           (left + len - 1) * sizeof (INT))
          by (rewrite sizeof_int; lia).
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
            (left + len - 1) n_pre
            (Znth (left + len - 1)
              (Znth (left + 1) left_table __default__List_Z) 0)
            (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial; lia.
        -- rewrite replace_Znth_Znth by lia.
           pose proof
             (IntArray2.missing_i_merge_to_full
               dp_l_pre (left + 1) n_pre n_pre left_table
               (Znth (left + 1) left_table __default__List_Z))
             as Hmerge_left.
           change
             (IntArray2.ElemArray.full
               (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray.full
               (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             in Hmerge_left.
           sep_apply_l_atomic Hmerge_left.
           ++ dump_pre_spatial; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_16 : solve_entail_wit_15_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH57 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as [Hlengths Hpartial].
  destruct Hlengths as [Hleft_shape Hrest].
  destruct Hrest as [Hright_shape Hdone].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Right.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
      with
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
       (left + len - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
         (left + len - 1) n_pre
         (Znth (left + len - 1)
            (Znth (left + 1) right_table __default__List_Z) 0)
         (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hright_row_len (left + 1) ltac:(lia)); lia).
      change
        (IntArray.full
           (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
           (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
           (Znth (left + 1) right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre (left + 1) n_pre n_pre right_table
           (Znth (left + 1) right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre +
           ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
          with
          (dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
           (left + len - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
             (left + len - 1) n_pre
             (Znth (left + len - 1)
                (Znth (left + 1) left_table __default__List_Z) 0)
             (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len (left + 1) ltac:(lia)); lia).
           change
             (IntArray.full
                (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
                (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
                (Znth (left + 1) left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre (left + 1) n_pre n_pre left_table
                (Znth (left + 1) left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try reflexivity.
    all: try lia.
    assert
      (Hpos_adjacent : forall k,
        0 <= k /\ k + 1 < Zlength pos_l ->
        Znth k pos_l 0 < Znth (k + 1) pos_l 0).
    {
      intros k Hk.
      apply PreH51.
      rewrite <- PreH48.
      exact Hk.
    }
    pose proof
      (streetlight_adjacent_strict_order__left_commit_d
         pos_l Hpos_adjacent (left + 1) (left + len - 1)
         ltac:(lia) ltac:(lia) ltac:(rewrite PreH48; lia)) as Hpos_order.
    nia.
Qed.

Lemma proof_of_solve_entail_wit_15_17 : solve_entail_wit_15_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)).
  Intros_p Hright_range.
  prop_apply_p
    (store_int_range
       (dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) left_table_2 __default__List_Z) 0)).
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  pose proof PreH53 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as [Hlengths Hpartial].
  destruct Hlengths as [Hleft_shape Hrest].
  destruct Hrest as [Hright_shape Hdone].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Left.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
      with
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
       (left + len - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
         (left + len - 1) n_pre
         (Znth (left + len - 1)
            (Znth (left + 1) right_table __default__List_Z) 0)
         (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hright_row_len (left + 1) ltac:(lia)); lia).
      change
        (IntArray.full
           (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
           (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
           (Znth (left + 1) right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre (left + 1) n_pre n_pre right_table
           (Znth (left + 1) right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre +
           ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
          with
          (dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
           (left + len - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
             (left + len - 1) n_pre
             (Znth (left + len - 1)
                (Znth (left + 1) left_table_2 __default__List_Z) 0)
             (Znth (left + 1) left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len (left + 1) ltac:(lia)); lia).
           change
             (IntArray.full
                (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre (left + 1) n_pre n_pre left_table_2
                (Znth (left + 1) left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_18 : solve_entail_wit_15_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)).
  Intros_p Hright_range.
  prop_apply_p
    (store_int_range
       (dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) left_table_2 __default__List_Z) 0)).
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  pose proof PreH53 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as [Hlengths Hpartial].
  destruct Hlengths as [Hleft_shape Hrest].
  destruct Hrest as [Hright_shape Hdone].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Left.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
      with
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
       (left + len - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
         (left + len - 1) n_pre
         (Znth (left + len - 1)
            (Znth (left + 1) right_table __default__List_Z) 0)
         (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hright_row_len (left + 1) ltac:(lia)); lia).
      change
        (IntArray.full
           (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
           (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
           (Znth (left + 1) right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre (left + 1) n_pre n_pre right_table
           (Znth (left + 1) right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre +
           ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
          with
          (dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
           (left + len - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
             (left + len - 1) n_pre
             (Znth (left + len - 1)
                (Znth (left + 1) left_table_2 __default__List_Z) 0)
             (Znth (left + 1) left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len (left + 1) ltac:(lia)); lia).
           change
             (IntArray.full
                (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre (left + 1) n_pre n_pre left_table_2
                (Znth (left + 1) left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_19 : solve_entail_wit_15_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)).
  Intros_p Hright_range.
  prop_apply_p
    (store_int_range
       (dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) left_table_2 __default__List_Z) 0)).
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  pose proof PreH53 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as [Hlengths Hpartial].
  destruct Hlengths as [Hleft_shape Hrest].
  destruct Hrest as [Hright_shape Hdone].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
      with
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
       (left + len - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
         (left + len - 1) n_pre
         (Znth (left + len - 1)
            (Znth (left + 1) right_table __default__List_Z) 0)
         (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hright_row_len (left + 1) ltac:(lia)); lia).
      change
        (IntArray.full
           (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
           (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
           (Znth (left + 1) right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre (left + 1) n_pre n_pre right_table
           (Znth (left + 1) right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre +
           ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
          with
          (dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
           (left + len - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
             (left + len - 1) n_pre
             (Znth (left + len - 1)
                (Znth (left + 1) left_table_2 __default__List_Z) 0)
             (Znth (left + 1) left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len (left + 1) ltac:(lia)); lia).
           change
             (IntArray.full
                (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre (left + 1) n_pre n_pre left_table_2
                (Znth (left + 1) left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_15_20 : solve_entail_wit_15_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)).
  Intros_p Hright_range.
  prop_apply_p
    (store_int_range
       (dp_l_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) left_table_2 __default__List_Z) 0)).
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  pose proof PreH53 as Hshape.
  unfold StreetlightLeftProgress, StreetlightLengthsDone,
    StreetlightTableShape in Hshape.
  destruct Hshape as [Hlengths Hpartial].
  destruct Hlengths as [Hleft_shape Hrest].
  destruct Hrest as [Hright_shape Hdone].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
      with
      (dp_r_pre + (left + 1) * n_pre * sizeof (INT) +
       (left + len - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + (left + 1) * n_pre * sizeof (INT))
         (left + len - 1) n_pre
         (Znth (left + len - 1)
            (Znth (left + 1) right_table __default__List_Z) 0)
         (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hright_row_len (left + 1) ltac:(lia)); lia).
      change
        (IntArray.full
           (dp_r_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
           (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre (left + 1)) n_pre
           (Znth (left + 1) right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre (left + 1) n_pre n_pre right_table
           (Znth (left + 1) right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre +
           ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
          with
          (dp_l_pre + (left + 1) * n_pre * sizeof (INT) +
           (left + len - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + (left + 1) * n_pre * sizeof (INT))
             (left + len - 1) n_pre
             (Znth (left + len - 1)
                (Znth (left + 1) left_table_2 __default__List_Z) 0)
             (Znth (left + 1) left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len (left + 1) ltac:(lia)); lia).
           change
             (IntArray.full
                (dp_l_pre + (left + 1) * n_pre * sizeof (INT)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre (left + 1)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre (left + 1) n_pre n_pre left_table_2
                (Znth (left + 1) left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_1 : solve_entail_wit_16_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_total_sum__right_remain_a
       power_l prefix_l_2 n_pre total PreH35 PreH42 PreH3)
    as Htotal_sum.
  pose proof
    (StreetlightLeftProgress_predecessor_finite__right_remain_a
       pos_l power_l left_table_2 right_table_2 n_pre start len left right
       __default__List_Z
       PreH34 PreH35 PreH36 PreH37 PreH38 ltac:(lia) PreH5 PreH10
       PreH12 PreH13 PreH14 PreH15 PreH16 PreH43)
    as Hfinite.
  destruct Hfinite as [Hfinite | Hfinite].
  - lia.
  - lia.
Qed.

Lemma proof_of_solve_entail_wit_16_2 : solve_entail_wit_16_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_total_sum__right_remain_a
       power_l prefix_l_2 n_pre total PreH35 PreH42 PreH3)
    as Htotal_sum.
  pose proof
    (StreetlightLeftProgress_predecessor_finite__right_remain_a
       pos_l power_l left_table_2 right_table_2 n_pre start len left right
       __default__List_Z
       PreH34 PreH35 PreH36 PreH37 PreH38 ltac:(lia) PreH5 PreH10
       PreH12 PreH13 PreH14 PreH15 PreH16 PreH43)
    as Hfinite.
  destruct Hfinite as [Hfinite | Hfinite].
  - lia.
  - lia.
Qed.

Lemma proof_of_solve_entail_wit_16_3 : solve_entail_wit_16_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_total_sum__right_remain_a
       power_l prefix_l_2 n_pre total PreH35 PreH42 PreH3)
    as Htotal_sum.
  pose proof
    (StreetlightLeftProgress_predecessor_finite__right_remain_a
       pos_l power_l left_table_2 right_table_2 n_pre start len left right
       __default__List_Z
       PreH34 PreH35 PreH36 PreH37 PreH38 ltac:(lia) PreH5 PreH10
       PreH12 PreH13 PreH14 PreH15 PreH16 PreH43)
    as Hfinite.
  destruct Hfinite as [Hfinite | Hfinite].
  - lia.
  - lia.
Qed.

Lemma proof_of_solve_entail_wit_16_4 : solve_entail_wit_16_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_total_sum__right_remain_a
       power_l prefix_l_2 n_pre total PreH35 PreH42 PreH3)
    as Htotal_sum.
  pose proof
    (StreetlightLeftProgress_predecessor_finite__right_remain_a
       pos_l power_l left_table_2 right_table_2 n_pre start len left right
       __default__List_Z
       PreH34 PreH35 PreH36 PreH37 PreH38 ltac:(lia) PreH5 PreH10
       PreH12 PreH13 PreH14 PreH15 PreH16 PreH43)
    as Hfinite.
  destruct Hfinite as [Hfinite | Hfinite].
  - lia.
  - lia.
Qed.

Lemma proof_of_solve_entail_wit_16_5 : solve_entail_wit_16_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH45 as Hshape_data.
  unfold StreetlightLeftProgress in Hshape_data.
  destruct Hshape_data as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left _].
  unfold StreetlightTableShape in Hshape_left.
  destruct Hshape_left as [Htable_len Hrow_len].
  assert (Hrow_default :
    Znth left left_table_2 __default__List_Z =
    Znth left left_table_2 (@nil Z)).
  { apply Znth_indep. lia. }
  pose proof
    (StreetlightLeftEntryCorrect_from_left_candidate__right_remain_a
       pos_l power_l prefix_l_2 left_table_2 right_table_2 n_pre total
       start len left right remain best __default__List_Z
       PreH36 PreH37 PreH38 PreH39 PreH40 PreH44 PreH3 ltac:(lia)
       PreH5 PreH10 PreH12 PreH13 PreH14 PreH15 PreH16 PreH21
       ltac:(lia) PreH45 ltac:(lia) PreH27
       ltac:(intros Hfinite; apply PreH29; lia))
    as Hentry.
  set (left_table :=
    replace_Znth left
      (replace_Znth right best (Znth left left_table_2 (@nil Z)))
      left_table_2).
  pose proof
    (StreetlightLeftProgress_update_cell__right_remain_a
       pos_l power_l left_table_2 right_table_2 n_pre start len left right
       best PreH45 ltac:(lia) PreH12 PreH14 PreH16)
    as Hupdated_progress.
  assert (Hready :
    StreetlightLeftEndpointReady pos_l power_l left_table right_table_2
      n_pre start len left).
  {
    unfold StreetlightLeftEndpointReady.
    split.
    - unfold left_table. exact Hupdated_progress.
    - simpl.
      replace (left + len - 1) with right by lia.
      unfold left_table.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same by
        (pose proof (Hrow_len left ltac:(lia)); lia).
      exact Hentry.
  }
  assert (Hpending_right :
    forall pending_right,
      start + len - 1 <= pending_right < n_pre ->
      Znth pending_right
        (Znth start left_table __default__List_Z) 0 = inf).
  {
    intros pending_right Hpending.
    unfold left_table.
    rewrite Znth_replace_Znth_Diff by lia.
    apply PreH42. exact Hpending.
  }
  assert (Hleft_start_inf :
    left = start ->
    Znth right (Znth left left_table __default__List_Z) 0 = inf).
  { intro Hcontra. lia. }
  assert (Hright_start_inf :
    right = start ->
    Znth right
      (Znth left right_table_2 __default__List_Z) 0 = inf).
  {
    intro Hright_start.
    rewrite Hright_start.
    apply PreH43. lia.
  }
  Left.
  Exists right_table_2 left_table prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT)) with
      (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    rewrite Hrow_default.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left left_table_2 (@nil Z))).
    + dump_pre_spatial. pose proof (Hrow_len left ltac:(lia)). lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           dp_l_pre left n_pre n_pre left_table_2
           (replace_Znth right best (Znth left left_table_2 (@nil Z)))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_l_pre n_pre left) n_pre
           (replace_Znth right best (Znth left left_table_2 (@nil Z))))
        with
        (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best (Znth left left_table_2 (@nil Z))))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold left_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_16_6 : solve_entail_wit_16_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst inf.
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hremaining :
      remain = sum power_l - sum (sublist (left + 1) (right + 1) power_l)).
  { eapply StreetlightPrefixProgress_remaining__right_remain_b; eauto; lia. }
  assert (Hselected :
      (Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 +
         (Znth (left + 1) pos_l 0 - Znth left pos_l 0) * remain) \/
      (Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 +
         (Znth right pos_l 0 - Znth left pos_l 0) * remain)).
  { left. split; assumption. }
  assert (Hready :
      StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
        n_pre start len left).
  { unfold updated_table, updated_row.
    eapply StreetlightLeftEndpointReady_after_best__right_remain_b;
      eauto; lia. }
  pose proof PreH45 as Hprogress_shape.
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths _].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hshape_left [_ _]].
  assert (Hpending_right :
      forall pending_right,
        start + len - 1 <= pending_right < n_pre ->
        Znth pending_right
          (Znth start updated_table __default__List_Z) 0 = 2147483647).
  { intros pending_right Hpending.
    unfold updated_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. exact Hpending.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - lia. }
  assert (Hleft_start :
      left = start ->
      Znth right (Znth left updated_table __default__List_Z) 0 = 2147483647).
  { intros Hcontra. lia. }
  assert (Hright_start :
      right = start ->
      Znth right (Znth left right_table_2 __default__List_Z) 0 = 2147483647).
  { intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia. }
  Left.
  Exists right_table_2 updated_table prefix_l_2.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
      dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold updated_row.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
      with
      (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre updated_row)
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold updated_table. cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_7 : solve_entail_wit_16_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst inf.
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hremaining :
      remain = sum power_l - sum (sublist (left + 1) (right + 1) power_l)).
  { eapply StreetlightPrefixProgress_remaining__right_remain_b; eauto; lia. }
  assert (Hselected :
      (Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 +
         (Znth (left + 1) pos_l 0 - Znth left pos_l 0) * remain) \/
      (Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 +
         (Znth right pos_l 0 - Znth left pos_l 0) * remain)).
  { left. split; assumption. }
  assert (Hready :
      StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
        n_pre start len left).
  { unfold updated_table, updated_row.
    eapply StreetlightLeftEndpointReady_after_best__right_remain_b;
      eauto; lia. }
  pose proof PreH45 as Hprogress_shape.
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths _].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hshape_left [_ _]].
  assert (Hpending_right :
      forall pending_right,
        start + len - 1 <= pending_right < n_pre ->
        Znth pending_right
          (Znth start updated_table __default__List_Z) 0 = 2147483647).
  { intros pending_right Hpending.
    unfold updated_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. exact Hpending.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - lia. }
  assert (Hleft_start :
      left = start ->
      Znth right (Znth left updated_table __default__List_Z) 0 = 2147483647).
  { intros Hcontra. lia. }
  assert (Hright_start :
      right = start ->
      Znth right (Znth left right_table_2 __default__List_Z) 0 = 2147483647).
  { intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia. }
  Right.
  Exists right_table_2 updated_table prefix_l_2.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
      dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold updated_row.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
      with
      (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre updated_row)
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold updated_table. cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_8 : solve_entail_wit_16_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst inf.
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hremaining :
      remain = sum power_l - sum (sublist (left + 1) (right + 1) power_l)).
  { eapply StreetlightPrefixProgress_remaining__right_remain_b; eauto; lia. }
  assert (Hselected :
      (Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 +
         (Znth (left + 1) pos_l 0 - Znth left pos_l 0) * remain) \/
      (Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 +
         (Znth right pos_l 0 - Znth left pos_l 0) * remain)).
  { left. split; assumption. }
  assert (Hready :
      StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
        n_pre start len left).
  { unfold updated_table, updated_row.
    eapply StreetlightLeftEndpointReady_after_best__right_remain_b;
      eauto; lia. }
  pose proof PreH45 as Hprogress_shape.
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths _].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hshape_left [_ _]].
  assert (Hpending_right :
      forall pending_right,
        start + len - 1 <= pending_right < n_pre ->
        Znth pending_right
          (Znth start updated_table __default__List_Z) 0 = 2147483647).
  { intros pending_right Hpending.
    unfold updated_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. exact Hpending.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - lia. }
  assert (Hleft_start :
      left = start ->
      Znth right (Znth left updated_table __default__List_Z) 0 = 2147483647).
  { intros Hcontra. lia. }
  assert (Hright_start :
      right = start ->
      Znth right (Znth left right_table_2 __default__List_Z) 0 = 2147483647).
  { intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia. }
  Right.
  Exists right_table_2 updated_table prefix_l_2.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
      dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold updated_row.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
      with
      (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre updated_row)
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold updated_table. cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_9 : solve_entail_wit_16_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst inf.
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hremaining :
      remain = sum power_l - sum (sublist (left + 1) (right + 1) power_l)).
  { eapply StreetlightPrefixProgress_remaining__right_remain_b; eauto; lia. }
  assert (Hselected :
      (Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 +
         (Znth (left + 1) pos_l 0 - Znth left pos_l 0) * remain) \/
      (Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 +
         (Znth right pos_l 0 - Znth left pos_l 0) * remain)).
  { left. split; assumption. }
  assert (Hready :
      StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
        n_pre start len left).
  { unfold updated_table, updated_row.
    eapply StreetlightLeftEndpointReady_after_best__right_remain_b;
      eauto; lia. }
  pose proof PreH45 as Hprogress_shape.
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths _].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hshape_left [_ _]].
  assert (Hpending_right :
      forall pending_right,
        start + len - 1 <= pending_right < n_pre ->
        Znth pending_right
          (Znth start updated_table __default__List_Z) 0 = 2147483647).
  { intros pending_right Hpending.
    unfold updated_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. exact Hpending.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - lia. }
  assert (Hleft_start :
      left = start ->
      Znth right (Znth left updated_table __default__List_Z) 0 = 2147483647).
  { intros Hcontra. lia. }
  assert (Hright_start :
      right = start ->
      Znth right (Znth left right_table_2 __default__List_Z) 0 = 2147483647).
  { intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia. }
  Left.
  Exists right_table_2 updated_table prefix_l_2.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
      dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold updated_row.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
      with
      (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre updated_row)
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold updated_table. cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_10 : solve_entail_wit_16_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst inf.
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hremaining :
      remain = sum power_l - sum (sublist (left + 1) (right + 1) power_l)).
  { eapply StreetlightPrefixProgress_remaining__right_remain_b; eauto; lia. }
  assert (Hselected :
      (Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 +
         (Znth (left + 1) pos_l 0 - Znth left pos_l 0) * remain) \/
      (Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 +
         (Znth right pos_l 0 - Znth left pos_l 0) * remain)).
  { left. split; assumption. }
  assert (Hready :
      StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
        n_pre start len left).
  { unfold updated_table, updated_row.
    eapply StreetlightLeftEndpointReady_after_best__right_remain_b;
      eauto; lia. }
  pose proof PreH45 as Hprogress_shape.
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths _].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hshape_left [_ _]].
  assert (Hpending_right :
      forall pending_right,
        start + len - 1 <= pending_right < n_pre ->
        Znth pending_right
          (Znth start updated_table __default__List_Z) 0 = 2147483647).
  { intros pending_right Hpending.
    unfold updated_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. exact Hpending.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - lia. }
  assert (Hleft_start :
      left = start ->
      Znth right (Znth left updated_table __default__List_Z) 0 = 2147483647).
  { intros Hcontra. lia. }
  assert (Hright_start :
      right = start ->
      Znth right (Znth left right_table_2 __default__List_Z) 0 = 2147483647).
  { intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia. }
  Left.
  Exists right_table_2 updated_table prefix_l_2.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
      dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold updated_row.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
      with
      (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre updated_row)
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold updated_table. cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_11 : solve_entail_wit_16_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_remaining__right_remain_c
      power_l prefix_l_2 n_pre total left right remain
      PreH37 PreH12 ltac:(lia) PreH16 PreH3 PreH21 PreH44)
    as Hremain_sum.
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    pose proof PreH45 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    tauto.
  }
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hready :
    StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
      n_pre start len left).
  {
    unfold updated_table, updated_row.
    eapply streetlight_left_endpoint_minimum_extend__right_remain_c;
      [ exact PreH36 | exact PreH37 | exact PreH5 | lia | exact PreH12
      | lia | exact PreH14 | exact PreH16 | exact PreH19 | exact PreH39
      | exact Hremain_sum | exact PreH45 | exact PreH26
      | intros Hfinite; apply PreH28; lia
      | intros Hfinite; apply PreH29; lia
      | left; split; [lia | exact PreH27] ].
  }
  Right.
  Exists right_table_2 updated_table prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    intros pending_right Hpending;
    unfold updated_table;
    rewrite (Znth_replace_Znth_Diff __default__List_Z left_table_2 left
      start updated_row) by (try rewrite Hleft_table_len; lia);
    apply PreH42;
    exact Hpending
  ].
  all: try solve [
    dump_pre_spatial;
    intros Hright_start;
    rewrite Hright_start;
    apply PreH43;
    lia
  ].
  all: try solve [dump_pre_spatial; exact Hready].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
    (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
  simpl in Hrow_merge.
  assert (Haddr :
    dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
    dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
  rewrite <- Haddr.
  sep_apply Hrow_merge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
    with
    (IntArray.full
      (dp_l_pre + left * n_pre * 4) n_pre updated_row)
    in Htable_merge.
  fold updated_row.
  sep_apply Htable_merge; try lia.
  cancel (IntArray.full pos_pre n_pre pos_l).
  cancel (IntArray.full power_pre n_pre power_l).
  cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
  cancel (IntArray2.full dp_l_pre n_pre n_pre updated_table).
  cancel (IntArray2.full dp_r_pre n_pre n_pre right_table_2).
Qed.

Lemma proof_of_solve_entail_wit_16_12 : solve_entail_wit_16_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_remaining__right_remain_c
      power_l prefix_l_2 n_pre total left right remain
      PreH37 PreH12 ltac:(lia) PreH16 PreH3 PreH21 PreH44)
    as Hremain_sum.
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    pose proof PreH45 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    tauto.
  }
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hready :
    StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
      n_pre start len left).
  {
    unfold updated_table, updated_row.
    eapply streetlight_left_endpoint_minimum_extend__right_remain_c;
      [ exact PreH36 | exact PreH37 | exact PreH5 | lia | exact PreH12
      | lia | exact PreH14 | exact PreH16 | exact PreH19 | exact PreH39
      | exact Hremain_sum | exact PreH45 | exact PreH26
      | intros Hfinite; apply PreH28; lia
      | intros Hfinite; apply PreH29; lia
      | left; split; [lia | exact PreH27] ].
  }
  Right.
  Exists right_table_2 updated_table prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    intros pending_right Hpending;
    unfold updated_table;
    rewrite (Znth_replace_Znth_Diff __default__List_Z left_table_2 left
      start updated_row) by (try rewrite Hleft_table_len; lia);
    apply PreH42;
    exact Hpending
  ].
  all: try solve [
    dump_pre_spatial;
    intros Hright_start;
    rewrite Hright_start;
    apply PreH43;
    lia
  ].
  all: try solve [dump_pre_spatial; exact Hready].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
    (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
  simpl in Hrow_merge.
  assert (Haddr :
    dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
    dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
  rewrite <- Haddr.
  sep_apply Hrow_merge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
    with
    (IntArray.full
      (dp_l_pre + left * n_pre * 4) n_pre updated_row)
    in Htable_merge.
  fold updated_row.
  sep_apply Htable_merge; try lia.
  cancel (IntArray.full pos_pre n_pre pos_l).
  cancel (IntArray.full power_pre n_pre power_l).
  cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
  cancel (IntArray2.full dp_l_pre n_pre n_pre updated_table).
  cancel (IntArray2.full dp_r_pre n_pre n_pre right_table_2).
Qed.

Lemma proof_of_solve_entail_wit_16_13 : solve_entail_wit_16_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_remaining__right_remain_c
      power_l prefix_l_2 n_pre total left right remain
      PreH37 PreH12 ltac:(lia) PreH16 PreH3 PreH21 PreH44)
    as Hremain_sum.
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    pose proof PreH45 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    tauto.
  }
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hready :
    StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
      n_pre start len left).
  {
    unfold updated_table, updated_row.
    eapply streetlight_left_endpoint_minimum_extend__right_remain_c;
      [ exact PreH36 | exact PreH37 | exact PreH5 | lia | exact PreH12
      | lia | exact PreH14 | exact PreH16 | exact PreH19 | exact PreH39
      | exact Hremain_sum | exact PreH45 | exact PreH26
      | intros Hfinite; apply PreH28; lia
      | intros Hfinite; apply PreH29; lia
      | right; split; [lia | exact PreH27] ].
  }
  Left.
  Exists right_table_2 updated_table prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    intros pending_right Hpending;
    unfold updated_table;
    rewrite (Znth_replace_Znth_Diff __default__List_Z left_table_2 left
      start updated_row) by (try rewrite Hleft_table_len; lia);
    apply PreH42;
    exact Hpending
  ].
  all: try solve [
    dump_pre_spatial;
    intros Hright_start;
    rewrite Hright_start;
    apply PreH43;
    lia
  ].
  all: try solve [dump_pre_spatial; exact Hready].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
    (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
  simpl in Hrow_merge.
  assert (Haddr :
    dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
    dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
  rewrite <- Haddr.
  sep_apply Hrow_merge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
    with
    (IntArray.full
      (dp_l_pre + left * n_pre * 4) n_pre updated_row)
    in Htable_merge.
  fold updated_row.
  sep_apply Htable_merge; try lia.
  cancel (IntArray.full pos_pre n_pre pos_l).
  cancel (IntArray.full power_pre n_pre power_l).
  cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
  cancel (IntArray2.full dp_l_pre n_pre n_pre updated_table).
  cancel (IntArray2.full dp_r_pre n_pre n_pre right_table_2).
Qed.

Lemma proof_of_solve_entail_wit_16_14 : solve_entail_wit_16_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (StreetlightPrefixProgress_remaining__right_remain_c
      power_l prefix_l_2 n_pre total left right remain
      PreH37 PreH12 ltac:(lia) PreH16 PreH3 PreH21 PreH44)
    as Hremain_sum.
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    pose proof PreH45 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    tauto.
  }
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hready :
    StreetlightLeftEndpointReady pos_l power_l updated_table right_table_2
      n_pre start len left).
  {
    unfold updated_table, updated_row.
    eapply streetlight_left_endpoint_minimum_extend__right_remain_c;
      [ exact PreH36 | exact PreH37 | exact PreH5 | lia | exact PreH12
      | lia | exact PreH14 | exact PreH16 | exact PreH19 | exact PreH39
      | exact Hremain_sum | exact PreH45 | exact PreH26
      | intros Hfinite; apply PreH28; lia
      | intros Hfinite; apply PreH29; lia
      | right; split; [lia | exact PreH27] ].
  }
  Left.
  Exists right_table_2 updated_table prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    intros pending_right Hpending;
    unfold updated_table;
    rewrite (Znth_replace_Znth_Diff __default__List_Z left_table_2 left
      start updated_row) by (try rewrite Hleft_table_len; lia);
    apply PreH42;
    exact Hpending
  ].
  all: try solve [
    dump_pre_spatial;
    intros Hright_start;
    rewrite Hright_start;
    apply PreH43;
    lia
  ].
  all: try solve [dump_pre_spatial; exact Hready].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
    (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
  simpl in Hrow_merge.
  assert (Haddr :
    dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT) =
    dp_l_pre + (left * n_pre + right) * sizeof (INT)) by lia.
  rewrite <- Haddr.
  sep_apply Hrow_merge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_l_pre left n_pre n_pre left_table_2 updated_row) as Htable_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_l_pre n_pre left) n_pre updated_row)
    with
    (IntArray.full
      (dp_l_pre + left * n_pre * 4) n_pre updated_row)
    in Htable_merge.
  fold updated_row.
  sep_apply Htable_merge; try lia.
  cancel (IntArray.full pos_pre n_pre pos_l).
  cancel (IntArray.full power_pre n_pre power_l).
  cancel (IntArray.full pre_pre (n_pre + 1) prefix_l_2).
  cancel (IntArray2.full dp_l_pre n_pre n_pre updated_table).
  cancel (IntArray2.full dp_r_pre n_pre n_pre right_table_2).
Qed.

Lemma proof_of_solve_entail_wit_16_15 : solve_entail_wit_16_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (row' := replace_Znth right best
    (Znth left left_table_2 __default__List_Z)).
  set (left_table := replace_Znth left row' left_table_2).
  assert (Hentry :
    StreetlightLeftEntryCorrect pos_l power_l start left right best).
  {
    eapply (streetlight_right_candidate_left_entry__right_remain_d
      pos_l power_l prefix_l_2 left_table_2 right_table_2
      n_pre start len left right total remain best inf
      __default__List_Z).
    - exact PreH1.
    - exact PreH36.
    - exact PreH37.
    - lia.
    - lia.
    - lia.
    - exact PreH14.
    - lia.
    - exact PreH19.
    - exact PreH3.
    - exact PreH21.
    - exact PreH27.
    - exact PreH23.
    - subst inf. nia.
    - left. exact PreH24.
    - exact PreH39.
    - exact PreH44.
    - exact PreH45.
  }
  assert (Hready :
    StreetlightLeftEndpointReady
      pos_l power_l left_table right_table_2 n_pre start len left).
  {
    unfold left_table, row'.
    eapply (streetlight_right_candidate_left_store__right_remain_d
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      best __default__List_Z);
      try eassumption; lia.
  }
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in PreH45.
    tauto.
  }
  assert (Hpending_right :
    forall pending_right,
      (start + len - 1 <= pending_right /\ pending_right < n_pre) ->
      Znth pending_right
        (Znth start left_table __default__List_Z) 0 = inf).
  {
    intros pending_right Hpending.
    unfold left_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. lia.
    - rewrite Hleft_table_len. lia.
    - rewrite Hleft_table_len. lia.
    - lia.
  }
  assert (Hright_sentinel :
    right = start ->
    Znth right (Znth left right_table_2 __default__List_Z) 0 = inf).
  {
    intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia.
  }
  Right.
  Exists right_table_2 left_table prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold row'.
      change
        (IntArray.full
          (dp_l_pre + left * n_pre * sizeof (INT)) n_pre row')
        with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_l_pre n_pre left) n_pre row').
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          dp_l_pre left n_pre n_pre left_table_2 row').
      * dump_pre_spatial. lia.
      * fold left_table. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_16_16 : solve_entail_wit_16_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (row' := replace_Znth right best
    (Znth left left_table_2 __default__List_Z)).
  set (left_table := replace_Znth left row' left_table_2).
  assert (Hentry :
    StreetlightLeftEntryCorrect pos_l power_l start left right best).
  {
    eapply (streetlight_right_candidate_left_entry__right_remain_d
      pos_l power_l prefix_l_2 left_table_2 right_table_2
      n_pre start len left right total remain best inf
      __default__List_Z).
    - exact PreH1.
    - exact PreH36.
    - exact PreH37.
    - lia.
    - lia.
    - lia.
    - exact PreH14.
    - lia.
    - exact PreH19.
    - exact PreH3.
    - exact PreH21.
    - exact PreH27.
    - exact PreH23.
    - subst inf. nia.
    - left. exact PreH24.
    - exact PreH39.
    - exact PreH44.
    - exact PreH45.
  }
  assert (Hready :
    StreetlightLeftEndpointReady
      pos_l power_l left_table right_table_2 n_pre start len left).
  {
    unfold left_table, row'.
    eapply (streetlight_right_candidate_left_store__right_remain_d
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      best __default__List_Z);
      try eassumption; lia.
  }
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in PreH45.
    tauto.
  }
  assert (Hpending_right :
    forall pending_right,
      (start + len - 1 <= pending_right /\ pending_right < n_pre) ->
      Znth pending_right
        (Znth start left_table __default__List_Z) 0 = inf).
  {
    intros pending_right Hpending.
    unfold left_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. lia.
    - rewrite Hleft_table_len. lia.
    - rewrite Hleft_table_len. lia.
    - lia.
  }
  assert (Hright_sentinel :
    right = start ->
    Znth right (Znth left right_table_2 __default__List_Z) 0 = inf).
  {
    intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia.
  }
  Right.
  Exists right_table_2 left_table prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold row'.
      change
        (IntArray.full
          (dp_l_pre + left * n_pre * sizeof (INT)) n_pre row')
        with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_l_pre n_pre left) n_pre row').
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          dp_l_pre left n_pre n_pre left_table_2 row').
      * dump_pre_spatial. lia.
      * fold left_table. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_16_17 : solve_entail_wit_16_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (row' := replace_Znth right best
    (Znth left left_table_2 __default__List_Z)).
  set (left_table := replace_Znth left row' left_table_2).
  assert (Hentry :
    StreetlightLeftEntryCorrect pos_l power_l start left right best).
  {
    eapply (streetlight_right_candidate_left_entry__right_remain_d
      pos_l power_l prefix_l_2 left_table_2 right_table_2
      n_pre start len left right total remain best inf
      __default__List_Z).
    - exact PreH1.
    - exact PreH36.
    - exact PreH37.
    - lia.
    - lia.
    - lia.
    - exact PreH14.
    - lia.
    - exact PreH19.
    - exact PreH3.
    - exact PreH21.
    - exact PreH27.
    - exact PreH23.
    - subst inf. nia.
    - right. rewrite PreH27. exact PreH24.
    - exact PreH39.
    - exact PreH44.
    - exact PreH45.
  }
  assert (Hready :
    StreetlightLeftEndpointReady
      pos_l power_l left_table right_table_2 n_pre start len left).
  {
    unfold left_table, row'.
    eapply (streetlight_right_candidate_left_store__right_remain_d
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      best __default__List_Z);
      try eassumption; lia.
  }
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in PreH45.
    tauto.
  }
  assert (Hpending_right :
    forall pending_right,
      (start + len - 1 <= pending_right /\ pending_right < n_pre) ->
      Znth pending_right
        (Znth start left_table __default__List_Z) 0 = inf).
  {
    intros pending_right Hpending.
    unfold left_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. lia.
    - rewrite Hleft_table_len. lia.
    - rewrite Hleft_table_len. lia.
    - lia.
  }
  assert (Hright_sentinel :
    right = start ->
    Znth right (Znth left right_table_2 __default__List_Z) 0 = inf).
  {
    intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia.
  }
  Left.
  Exists right_table_2 left_table prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold row'.
      change
        (IntArray.full
          (dp_l_pre + left * n_pre * sizeof (INT)) n_pre row')
        with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_l_pre n_pre left) n_pre row').
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          dp_l_pre left n_pre n_pre left_table_2 row').
      * dump_pre_spatial. lia.
      * fold left_table. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_16_18 : solve_entail_wit_16_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (row' := replace_Znth right best
    (Znth left left_table_2 __default__List_Z)).
  set (left_table := replace_Znth left row' left_table_2).
  assert (Hentry :
    StreetlightLeftEntryCorrect pos_l power_l start left right best).
  {
    eapply (streetlight_right_candidate_left_entry__right_remain_d
      pos_l power_l prefix_l_2 left_table_2 right_table_2
      n_pre start len left right total remain best inf
      __default__List_Z).
    - exact PreH1.
    - exact PreH36.
    - exact PreH37.
    - lia.
    - lia.
    - lia.
    - exact PreH14.
    - lia.
    - exact PreH19.
    - exact PreH3.
    - exact PreH21.
    - exact PreH27.
    - exact PreH23.
    - subst inf. nia.
    - right. rewrite PreH27. exact PreH24.
    - exact PreH39.
    - exact PreH44.
    - exact PreH45.
  }
  assert (Hready :
    StreetlightLeftEndpointReady
      pos_l power_l left_table right_table_2 n_pre start len left).
  {
    unfold left_table, row'.
    eapply (streetlight_right_candidate_left_store__right_remain_d
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      best __default__List_Z);
      try eassumption; lia.
  }
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in PreH45.
    tauto.
  }
  assert (Hpending_right :
    forall pending_right,
      (start + len - 1 <= pending_right /\ pending_right < n_pre) ->
      Znth pending_right
        (Znth start left_table __default__List_Z) 0 = inf).
  {
    intros pending_right Hpending.
    unfold left_table.
    rewrite Znth_replace_Znth_Diff.
    - apply PreH42. lia.
    - rewrite Hleft_table_len. lia.
    - rewrite Hleft_table_len. lia.
    - lia.
  }
  assert (Hright_sentinel :
    right = start ->
    Znth right (Znth left right_table_2 __default__List_Z) 0 = inf).
  {
    intros Hright_start.
    rewrite Hright_start.
    apply PreH43. lia.
  }
  Left.
  Exists right_table_2 left_table prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold row'.
      change
        (IntArray.full
          (dp_l_pre + left * n_pre * sizeof (INT)) n_pre row')
        with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_l_pre n_pre left) n_pre row').
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          dp_l_pre left n_pre n_pre left_table_2 row').
      * dump_pre_spatial. lia.
      * fold left_table. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_16_19 : solve_entail_wit_16_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists right_table_2
    (replace_Znth left
      (replace_Znth right best
        (Znth left left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT)) with
      (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + change (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
        (replace_Znth right best
          (Znth left left_table_2 __default__List_Z))) with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_l_pre n_pre left) n_pre
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          dp_l_pre left n_pre n_pre left_table_2
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))).
      * dump_pre_spatial. lia.
      * cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; auto].
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; intros Hright; rewrite Hright;
                    exact (PreH43 left ltac:(lia))].
    all: try solve [
      dump_pre_spatial;
      intros pending_right Hpending;
      pose proof PreH45 as Hshape_pending;
      unfold StreetlightLeftProgress, StreetlightLengthsDone,
        StreetlightTableShape in Hshape_pending;
      destruct Hshape_pending as [[[Htable_len_pending _] _] _];
      rewrite Znth_replace_Znth_Diff by lia;
      apply PreH42; lia
    ].
    all: dump_pre_spatial.
    assert (Hprogress_updated :
      StreetlightLeftProgress pos_l power_l
        (replace_Znth left
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))
          left_table_2)
        right_table_2 n_pre start len left).
    { exact (StreetlightLeftProgress_replace_current__right_remain_e
        pos_l power_l left_table_2 right_table_2 n_pre start len left
        right best __default__List_Z ltac:(lia) ltac:(lia) PreH14 PreH45). }
    assert (Hentry :
      StreetlightLeftEntryCorrect pos_l power_l start left right best).
    { exact (StreetlightLeftEntryCorrect_right_choice__right_remain_e
        pos_l power_l prefix_l_2 left_table_2 right_table_2 n_pre start
        len left right total remain best __default__List_Z PreH36 PreH37
        ltac:(lia) PreH14 ltac:(lia) PreH10 PreH3 PreH21
        ltac:(rewrite <- PreH1; exact PreH23) PreH24 PreH27 PreH44 PreH45). }
    pose proof PreH45 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    destruct Hshape as [[[Htable_len Hrow_len] _] _].
    unfold StreetlightLeftEndpointReady.
    split.
    + exact Hprogress_updated.
    + replace (left + len - 1) with right by lia.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same.
      * exact Hentry.
      * rewrite (Znth_indep left_table_2 left __default__List_Z nil) by lia.
        rewrite Hrow_len by lia.
        lia.
Qed.

Lemma proof_of_solve_entail_wit_16_20 : solve_entail_wit_16_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists right_table_2
    (replace_Znth left
      (replace_Znth right best
        (Znth left left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  split_pure_spatial.
  - replace (dp_l_pre + (left * n_pre + right) * sizeof (INT)) with
      (dp_l_pre + left * n_pre * sizeof (INT) + right * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_l_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + change (IntArray.full
        (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
        (replace_Znth right best
          (Znth left left_table_2 __default__List_Z))) with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_l_pre n_pre left) n_pre
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          dp_l_pre left n_pre n_pre left_table_2
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))).
      * dump_pre_spatial. lia.
      * cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; auto].
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; intros Hright; rewrite Hright;
                    exact (PreH43 left ltac:(lia))].
    all: try solve [
      dump_pre_spatial;
      intros pending_right Hpending;
      pose proof PreH45 as Hshape_pending;
      unfold StreetlightLeftProgress, StreetlightLengthsDone,
        StreetlightTableShape in Hshape_pending;
      destruct Hshape_pending as [[[Htable_len_pending _] _] _];
      rewrite Znth_replace_Znth_Diff by lia;
      apply PreH42; lia
    ].
    all: dump_pre_spatial.
    assert (Hprogress_updated :
      StreetlightLeftProgress pos_l power_l
        (replace_Znth left
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))
          left_table_2)
        right_table_2 n_pre start len left).
    { exact (StreetlightLeftProgress_replace_current__right_remain_e
        pos_l power_l left_table_2 right_table_2 n_pre start len left
        right best __default__List_Z ltac:(lia) ltac:(lia) PreH14 PreH45). }
    assert (Hentry :
      StreetlightLeftEntryCorrect pos_l power_l start left right best).
    { exact (StreetlightLeftEntryCorrect_right_choice__right_remain_e
        pos_l power_l prefix_l_2 left_table_2 right_table_2 n_pre start
        len left right total remain best __default__List_Z PreH36 PreH37
        ltac:(lia) PreH14 ltac:(lia) PreH10 PreH3 PreH21
        ltac:(rewrite <- PreH1; exact PreH23) PreH24 PreH27 PreH44 PreH45). }
    pose proof PreH45 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    destruct Hshape as [[[Htable_len Hrow_len] _] _].
    unfold StreetlightLeftEndpointReady.
    split.
    + exact Hprogress_updated.
    + replace (left + len - 1) with right by lia.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same.
      * exact Hentry.
      * rewrite (Znth_indep left_table_2 left __default__List_Z nil) by lia.
        rewrite Hrow_len by lia.
        lia.
Qed.

Lemma proof_of_solve_entail_wit_16_21 : solve_entail_wit_16_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; auto].
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; intros; apply PreH47; lia].
    all: try solve [dump_pre_spatial; intros Hleft; rewrite Hleft;
                    exact (PreH47 (start + len - 1) ltac:(lia))].
    all: dump_pre_spatial.
    pose proof PreH50 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    destruct Hshape as [[Hleft_shape _] _].
    destruct Hleft_shape as [Htable_len _].
    unfold StreetlightLeftEndpointReady.
    split.
    + exact PreH50.
    + unfold StreetlightLeftEntryCorrect.
      right; right.
      repeat split; try lia.
      replace left with start by lia.
      rewrite (Znth_indep left_table_2 start nil __default__List_Z) by lia.
      rewrite <- PreH20.
      apply PreH47; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_22 : solve_entail_wit_16_22.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; auto].
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; intros; apply PreH47; lia].
    all: try solve [dump_pre_spatial; intros Hleft; rewrite Hleft;
                    exact (PreH47 (start + len - 1) ltac:(lia))].
    all: dump_pre_spatial.
    pose proof PreH50 as Hshape.
    unfold StreetlightLeftProgress, StreetlightLengthsDone,
      StreetlightTableShape in Hshape.
    destruct Hshape as [[Hleft_shape _] _].
    destruct Hleft_shape as [Htable_len _].
    unfold StreetlightLeftEndpointReady.
    split.
    + exact PreH50.
    + unfold StreetlightLeftEntryCorrect.
      right; right.
      repeat split; try lia.
      replace left with start by lia.
      rewrite (Znth_indep left_table_2 start nil __default__List_Z) by lia.
      rewrite <- PreH20.
      apply PreH47; lia.
Qed.

Lemma proof_of_solve_entail_wit_17_1 : solve_entail_wit_17_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_prefix_remaining_bounds__right_first
      power_l prefix_l n_pre left right total
      PreH27 PreH30 PreH36 PreH4 PreH13 ltac:(lia) PreH17 PreH19)
    as Hremain.
  destruct Hremain as [Hremain_lower Hremain_upper].
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: auto.
Qed.

Lemma proof_of_solve_entail_wit_17_2 : solve_entail_wit_17_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_prefix_remaining_bounds__right_first
      power_l prefix_l n_pre left right total
      PreH27 PreH30 PreH36 PreH4 PreH13 ltac:(lia) PreH17 PreH19)
    as Hremain.
  destruct Hremain as [Hremain_lower Hremain_upper].
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: auto.
Qed.

Lemma proof_of_solve_entail_wit_17_3 : solve_entail_wit_17_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_prefix_remaining_bounds__right_first
      power_l prefix_l n_pre left right total
      PreH27 PreH30 PreH36 PreH4 PreH13 ltac:(lia) PreH17 PreH19)
    as Hremain.
  destruct Hremain as [Hremain_lower Hremain_upper].
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: auto.
Qed.

Lemma proof_of_solve_entail_wit_17_4 : solve_entail_wit_17_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_prefix_remaining_bounds__right_first
      power_l prefix_l n_pre left right total
      PreH27 PreH30 PreH36 PreH4 PreH13 ltac:(lia) PreH17 PreH19)
    as Hremain.
  destruct Hremain as [Hremain_lower Hremain_upper].
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: auto.
Qed.

Lemma proof_of_solve_entail_wit_18_1 : solve_entail_wit_18_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_second
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left right total inf
       PreH29 PreH30 PreH31 PreH32 PreH33 PreH39 PreH7
       ltac:(lia) PreH5 PreH14 PreH16 PreH17 PreH18 PreH4 PreH20
       PreH40 PreH1) as Hpredecessor_bounds.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_18_2 : solve_entail_wit_18_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_second
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left right total inf
       PreH29 PreH30 PreH31 PreH32 PreH33 PreH39 PreH7
       ltac:(lia) PreH5 PreH14 PreH16 PreH17 PreH18 PreH4 PreH20
       PreH40 PreH1) as Hpredecessor_bounds.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_18_3 : solve_entail_wit_18_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_second
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left right total inf
       PreH29 PreH30 PreH31 PreH32 PreH33 PreH39 PreH7
       ltac:(lia) PreH5 PreH14 PreH16 PreH17 PreH18 PreH4 PreH20
       PreH40 PreH1) as Hpredecessor_bounds.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_18_4 : solve_entail_wit_18_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_second
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left right total inf
       PreH29 PreH30 PreH31 PreH32 PreH33 PreH39 PreH7
       ltac:(lia) PreH5 PreH14 PreH16 PreH17 PreH18 PreH4 PreH20
       PreH40 PreH1) as Hpredecessor_bounds.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solve_entail_wit_19_1 : solve_entail_wit_19_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH33 left ltac:(lia)) as Hleft_bounds.
  pose proof (PreH33 right ltac:(lia)) as Hright_bounds.
  pose proof
    (streetlight_strict_positions__right_choose
       pos_l n_pre left right PreH34 ltac:(lia) ltac:(lia) ltac:(lia))
    as Hpositions_ordered.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      nia.
Qed.

Lemma proof_of_solve_entail_wit_19_2 : solve_entail_wit_19_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH33 left ltac:(lia)) as Hleft_bounds.
  pose proof (PreH33 right ltac:(lia)) as Hright_bounds.
  pose proof
    (streetlight_strict_positions__right_choose
       pos_l n_pre left right PreH34 ltac:(lia) ltac:(lia) ltac:(lia))
    as Hpositions_ordered.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      nia.
Qed.

Lemma proof_of_solve_entail_wit_19_3 : solve_entail_wit_19_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH33 left ltac:(lia)) as Hleft_bounds.
  pose proof (PreH33 right ltac:(lia)) as Hright_bounds.
  pose proof
    (streetlight_strict_positions__right_choose
       pos_l n_pre left right PreH34 ltac:(lia) ltac:(lia) ltac:(lia))
    as Hpositions_ordered.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      nia.
Qed.

Lemma proof_of_solve_entail_wit_19_4 : solve_entail_wit_19_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH33 left ltac:(lia)) as Hleft_bounds.
  pose proof (PreH33 right ltac:(lia)) as Hright_bounds.
  pose proof
    (streetlight_strict_positions__right_choose
       pos_l n_pre left right PreH34 ltac:(lia) ltac:(lia) ltac:(lia))
    as Hpositions_ordered.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      nia.
Qed.

Lemma proof_of_solve_entail_wit_20_1 : solve_entail_wit_20_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH44 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_values].
  assert (Hpower_sum : sum power_l = total).
  { specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  assert (Hposition_adjacent :
    forall k, 0 <= k -> k + 1 < Zlength pos_l ->
      Znth k pos_l 0 < Znth (k + 1) pos_l 0).
  { intros k Hk Hnext.
    apply PreH37.
    lia. }
  assert (Hposition_bounds :
    forall k, 0 <= k < Zlength pos_l ->
      0 <= Znth k pos_l 0 <= 8000).
  { intros k Hk.
    apply PreH36.
    lia. }
  assert (Hpower_nonnegative :
    forall k, 0 <= k < Zlength power_l -> 0 <= Znth k power_l 0).
  { intros k Hk.
    specialize (PreH38 k ltac:(lia)).
    lia. }
  assert (Hright_bounds :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 <=
      (len - 2) * 40000000).
  { pose proof PreH45 as Hready.
    unfold StreetlightLeftEndpointReady in Hready.
    destruct Hready as [Hleft_progress Hleft_entry].
    unfold StreetlightLeftProgress in Hleft_progress.
    destruct Hleft_progress as [Hlengths_done Hfinished_lefts].
    unfold StreetlightLengthsDone in Hlengths_done.
    destruct Hlengths_done as [Hleft_shape [Hright_shape Hdone]].
    unfold StreetlightTableShape in Hright_shape.
    destruct Hright_shape as [Hright_length Hright_rows].
    assert (Hright_row_default :
      Znth left right_table __default__List_Z =
      Znth left right_table nil).
    { apply Znth_indep.
      lia. }
    pose proof PreH1 as Hright_finite.
    rewrite Hright_row_default in Hright_finite.
    rewrite Hright_row_default.
    specialize
      (Hdone (len - 1) left (right - 1)
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold StreetlightIntervalCorrect in Hdone.
    destruct Hdone as [Hleft_previous Hright_previous].
    unfold StreetlightRightEntryCorrect in Hright_previous.
    destruct Hright_previous as [Hbase | [Hminimum | Hsentinel]].
    - destruct Hbase as [Hleft_start [Hright_start Hvalue]].
      lia.
    - destruct Hminimum as [Hstart_before Hminimum].
      unfold StreetlightEndpointMinimum,
        MaxMinLib.MaxMin.min_value_of_subset,
        MaxMinLib.MaxMin.min_object_of_subset in Hminimum.
      destruct Hminimum as [cost [[Hplan Hleast] ->]].
      pose proof
        (StreetlightPlan_cost_bounds__right_bounds_a
           pos_l power_l start left (right - 1) (right - 1)
           (Znth (right - 1) (Znth left right_table nil) 0)
           Hplan
           Hposition_adjacent Hposition_bounds ltac:(lia)
           Hpower_nonnegative ltac:(lia))
        as Hcost_bounds.
      lia.
    - destruct Hsentinel as [Hleft_before [Hright_start Hvalue]].
      lia.
  }
  destruct Hright_bounds as [Hright_nonnegative Hright_upper].
  Left.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_20_2 : solve_entail_wit_20_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH44 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_values].
  assert (Hpower_sum : sum power_l = total).
  { specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  assert (Hposition_adjacent :
    forall k, 0 <= k -> k + 1 < Zlength pos_l ->
      Znth k pos_l 0 < Znth (k + 1) pos_l 0).
  { intros k Hk Hnext.
    apply PreH37.
    lia. }
  assert (Hposition_bounds :
    forall k, 0 <= k < Zlength pos_l ->
      0 <= Znth k pos_l 0 <= 8000).
  { intros k Hk.
    apply PreH36.
    lia. }
  assert (Hpower_nonnegative :
    forall k, 0 <= k < Zlength power_l -> 0 <= Znth k power_l 0).
  { intros k Hk.
    specialize (PreH38 k ltac:(lia)).
    lia. }
  assert (Hright_bounds :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 <=
      (len - 2) * 40000000).
  { pose proof PreH45 as Hready.
    unfold StreetlightLeftEndpointReady in Hready.
    destruct Hready as [Hleft_progress Hleft_entry].
    unfold StreetlightLeftProgress in Hleft_progress.
    destruct Hleft_progress as [Hlengths_done Hfinished_lefts].
    unfold StreetlightLengthsDone in Hlengths_done.
    destruct Hlengths_done as [Hleft_shape [Hright_shape Hdone]].
    unfold StreetlightTableShape in Hright_shape.
    destruct Hright_shape as [Hright_length Hright_rows].
    assert (Hright_row_default :
      Znth left right_table __default__List_Z =
      Znth left right_table nil).
    { apply Znth_indep.
      lia. }
    pose proof PreH1 as Hright_finite.
    rewrite Hright_row_default in Hright_finite.
    rewrite Hright_row_default.
    specialize
      (Hdone (len - 1) left (right - 1)
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold StreetlightIntervalCorrect in Hdone.
    destruct Hdone as [Hleft_previous Hright_previous].
    unfold StreetlightRightEntryCorrect in Hright_previous.
    destruct Hright_previous as [Hbase | [Hminimum | Hsentinel]].
    - destruct Hbase as [Hleft_start [Hright_start Hvalue]].
      lia.
    - destruct Hminimum as [Hstart_before Hminimum].
      unfold StreetlightEndpointMinimum,
        MaxMinLib.MaxMin.min_value_of_subset,
        MaxMinLib.MaxMin.min_object_of_subset in Hminimum.
      destruct Hminimum as [cost [[Hplan Hleast] ->]].
      pose proof
        (StreetlightPlan_cost_bounds__right_bounds_a
           pos_l power_l start left (right - 1) (right - 1)
           (Znth (right - 1) (Znth left right_table nil) 0)
           Hplan
           Hposition_adjacent Hposition_bounds ltac:(lia)
           Hpower_nonnegative ltac:(lia))
        as Hcost_bounds.
      lia.
    - destruct Hsentinel as [Hleft_before [Hright_start Hvalue]].
      lia.
  }
  destruct Hright_bounds as [Hright_nonnegative Hright_upper].
  Left.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_20_3 : solve_entail_wit_20_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH44 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_values].
  assert (Hpower_sum : sum power_l = total).
  { specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  assert (Hposition_adjacent :
    forall k, 0 <= k -> k + 1 < Zlength pos_l ->
      Znth k pos_l 0 < Znth (k + 1) pos_l 0).
  { intros k Hk Hnext.
    apply PreH37.
    lia. }
  assert (Hposition_bounds :
    forall k, 0 <= k < Zlength pos_l ->
      0 <= Znth k pos_l 0 <= 8000).
  { intros k Hk.
    apply PreH36.
    lia. }
  assert (Hpower_nonnegative :
    forall k, 0 <= k < Zlength power_l -> 0 <= Znth k power_l 0).
  { intros k Hk.
    specialize (PreH38 k ltac:(lia)).
    lia. }
  assert (Hright_bounds :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 <=
      (len - 2) * 40000000).
  { pose proof PreH45 as Hready.
    unfold StreetlightLeftEndpointReady in Hready.
    destruct Hready as [Hleft_progress Hleft_entry].
    unfold StreetlightLeftProgress in Hleft_progress.
    destruct Hleft_progress as [Hlengths_done Hfinished_lefts].
    unfold StreetlightLengthsDone in Hlengths_done.
    destruct Hlengths_done as [Hleft_shape [Hright_shape Hdone]].
    unfold StreetlightTableShape in Hright_shape.
    destruct Hright_shape as [Hright_length Hright_rows].
    assert (Hright_row_default :
      Znth left right_table __default__List_Z =
      Znth left right_table nil).
    { apply Znth_indep.
      lia. }
    pose proof PreH1 as Hright_finite.
    rewrite Hright_row_default in Hright_finite.
    rewrite Hright_row_default.
    specialize
      (Hdone (len - 1) left (right - 1)
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold StreetlightIntervalCorrect in Hdone.
    destruct Hdone as [Hleft_previous Hright_previous].
    unfold StreetlightRightEntryCorrect in Hright_previous.
    destruct Hright_previous as [Hbase | [Hminimum | Hsentinel]].
    - destruct Hbase as [Hleft_start [Hright_start Hvalue]].
      lia.
    - destruct Hminimum as [Hstart_before Hminimum].
      unfold StreetlightEndpointMinimum,
        MaxMinLib.MaxMin.min_value_of_subset,
        MaxMinLib.MaxMin.min_object_of_subset in Hminimum.
      destruct Hminimum as [cost [[Hplan Hleast] ->]].
      pose proof
        (StreetlightPlan_cost_bounds__right_bounds_a
           pos_l power_l start left (right - 1) (right - 1)
           (Znth (right - 1) (Znth left right_table nil) 0)
           Hplan
           Hposition_adjacent Hposition_bounds ltac:(lia)
           Hpower_nonnegative ltac:(lia))
        as Hcost_bounds.
      lia.
    - destruct Hsentinel as [Hleft_before [Hright_start Hvalue]].
      lia.
  }
  destruct Hright_bounds as [Hright_nonnegative Hright_upper].
  Right.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_20_4 : solve_entail_wit_20_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH44 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_values].
  assert (Hpower_sum : sum power_l = total).
  { specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  assert (Hposition_adjacent :
    forall k, 0 <= k -> k + 1 < Zlength pos_l ->
      Znth k pos_l 0 < Znth (k + 1) pos_l 0).
  { intros k Hk Hnext.
    apply PreH37.
    lia. }
  assert (Hposition_bounds :
    forall k, 0 <= k < Zlength pos_l ->
      0 <= Znth k pos_l 0 <= 8000).
  { intros k Hk.
    apply PreH36.
    lia. }
  assert (Hpower_nonnegative :
    forall k, 0 <= k < Zlength power_l -> 0 <= Znth k power_l 0).
  { intros k Hk.
    specialize (PreH38 k ltac:(lia)).
    lia. }
  assert (Hright_bounds :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 <=
      (len - 2) * 40000000).
  { pose proof PreH45 as Hready.
    unfold StreetlightLeftEndpointReady in Hready.
    destruct Hready as [Hleft_progress Hleft_entry].
    unfold StreetlightLeftProgress in Hleft_progress.
    destruct Hleft_progress as [Hlengths_done Hfinished_lefts].
    unfold StreetlightLengthsDone in Hlengths_done.
    destruct Hlengths_done as [Hleft_shape [Hright_shape Hdone]].
    unfold StreetlightTableShape in Hright_shape.
    destruct Hright_shape as [Hright_length Hright_rows].
    assert (Hright_row_default :
      Znth left right_table __default__List_Z =
      Znth left right_table nil).
    { apply Znth_indep.
      lia. }
    pose proof PreH1 as Hright_finite.
    rewrite Hright_row_default in Hright_finite.
    rewrite Hright_row_default.
    specialize
      (Hdone (len - 1) left (right - 1)
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold StreetlightIntervalCorrect in Hdone.
    destruct Hdone as [Hleft_previous Hright_previous].
    unfold StreetlightRightEntryCorrect in Hright_previous.
    destruct Hright_previous as [Hbase | [Hminimum | Hsentinel]].
    - destruct Hbase as [Hleft_start [Hright_start Hvalue]].
      lia.
    - destruct Hminimum as [Hstart_before Hminimum].
      unfold StreetlightEndpointMinimum,
        MaxMinLib.MaxMin.min_value_of_subset,
        MaxMinLib.MaxMin.min_object_of_subset in Hminimum.
      destruct Hminimum as [cost [[Hplan Hleast] ->]].
      pose proof
        (StreetlightPlan_cost_bounds__right_bounds_a
           pos_l power_l start left (right - 1) (right - 1)
           (Znth (right - 1) (Znth left right_table nil) 0)
           Hplan
           Hposition_adjacent Hposition_bounds ltac:(lia)
           Hpower_nonnegative ltac:(lia))
        as Hcost_bounds.
      lia.
    - destruct Hsentinel as [Hleft_before [Hright_start Hvalue]].
      lia.
  }
  destruct Hright_bounds as [Hright_nonnegative Hright_upper].
  Right.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_20_5 : solve_entail_wit_20_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_bounds_b
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start total len left right inf
       PreH30 PreH31 PreH32 PreH33 PreH34 PreH8
       ltac:(lia) PreH15 PreH17 PreH18 PreH19 ltac:(lia) PreH21
       PreH40 PreH6 PreH1 PreH41) as Hprev_bounds.
  Left.
  repeat (split_pure_spatial || split_pures);
    try solve [cancel | dump_pre_spatial; auto | dump_pre_spatial; lia].
Qed.

Lemma proof_of_solve_entail_wit_20_6 : solve_entail_wit_20_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_bounds_b
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start total len left right inf
       PreH30 PreH31 PreH32 PreH33 PreH34 PreH8
       ltac:(lia) PreH15 PreH17 PreH18 PreH19 ltac:(lia) PreH21
       PreH40 PreH6 PreH1 PreH41) as Hprev_bounds.
  Left.
  repeat (split_pure_spatial || split_pures);
    try solve [cancel | dump_pre_spatial; auto | dump_pre_spatial; lia].
Qed.

Lemma proof_of_solve_entail_wit_20_7 : solve_entail_wit_20_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_bounds_b
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start total len left right inf
       PreH30 PreH31 PreH32 PreH33 PreH34 PreH8
       ltac:(lia) PreH15 PreH17 PreH18 PreH19 ltac:(lia) PreH21
       PreH40 PreH6 PreH1 PreH41) as Hprev_bounds.
  Right.
  repeat (split_pure_spatial || split_pures);
    try solve [cancel | dump_pre_spatial; auto | dump_pre_spatial; lia].
Qed.

Lemma proof_of_solve_entail_wit_20_8 : solve_entail_wit_20_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_right_predecessor_bounds__right_bounds_b
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start total len left right inf
       PreH30 PreH31 PreH32 PreH33 PreH34 PreH8
       ltac:(lia) PreH15 PreH17 PreH18 PreH19 ltac:(lia) PreH21
       PreH40 PreH6 PreH1 PreH41) as Hprev_bounds.
  Right.
  repeat (split_pure_spatial || split_pures);
    try solve [cancel | dump_pre_spatial; auto | dump_pre_spatial; lia].
Qed.

Lemma proof_of_solve_entail_wit_21_1 : solve_entail_wit_21_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH38 right ltac:(lia)) as Hpos_right.
  pose proof (PreH38 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH39 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  assert (Hdiff_nonneg :
    0 <= Znth right pos_l 0 - Znth (right - 1) pos_l 0) by lia.
  assert (Hdiff_le :
    Znth right pos_l 0 - Znth (right - 1) pos_l 0 <= 8000) by lia.
  assert (Hremain_nonneg :
    0 <= total - (Znth right prefix_l 0 - Znth left prefix_l 0)) by lia.
  pose proof (Z.mul_le_mono_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0) 8000
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) 5000
    Hdiff_nonneg Hdiff_le Hremain_nonneg PreH10) as Hproduct_le.
  pose proof (Z.mul_nonneg_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0)
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0))
    Hdiff_nonneg Hremain_nonneg) as Hproduct_nonneg.
  assert (Hcandidate_nonneg :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0))) by lia.
  assert (Hcandidate_le :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) <=
    (len - 1) * 40000000) by lia.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_solve_entail_wit_21_2 : solve_entail_wit_21_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH38 right ltac:(lia)) as Hpos_right.
  pose proof (PreH38 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH39 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  assert (Hdiff_nonneg :
    0 <= Znth right pos_l 0 - Znth (right - 1) pos_l 0) by lia.
  assert (Hdiff_le :
    Znth right pos_l 0 - Znth (right - 1) pos_l 0 <= 8000) by lia.
  assert (Hremain_nonneg :
    0 <= total - (Znth right prefix_l 0 - Znth left prefix_l 0)) by lia.
  pose proof (Z.mul_le_mono_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0) 8000
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) 5000
    Hdiff_nonneg Hdiff_le Hremain_nonneg PreH10) as Hproduct_le.
  pose proof (Z.mul_nonneg_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0)
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0))
    Hdiff_nonneg Hremain_nonneg) as Hproduct_nonneg.
  assert (Hcandidate_nonneg :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0))) by lia.
  assert (Hcandidate_le :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) <=
    (len - 1) * 40000000) by lia.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_solve_entail_wit_21_3 : solve_entail_wit_21_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH38 right ltac:(lia)) as Hpos_right.
  pose proof (PreH38 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH39 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  assert (Hdiff_nonneg :
    0 <= Znth right pos_l 0 - Znth (right - 1) pos_l 0) by lia.
  assert (Hdiff_le :
    Znth right pos_l 0 - Znth (right - 1) pos_l 0 <= 8000) by lia.
  assert (Hremain_nonneg :
    0 <= total - (Znth right prefix_l 0 - Znth left prefix_l 0)) by lia.
  pose proof (Z.mul_le_mono_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0) 8000
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) 5000
    Hdiff_nonneg Hdiff_le Hremain_nonneg PreH10) as Hproduct_le.
  pose proof (Z.mul_nonneg_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0)
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0))
    Hdiff_nonneg Hremain_nonneg) as Hproduct_nonneg.
  assert (Hcandidate_nonneg :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0))) by lia.
  assert (Hcandidate_le :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) <=
    (len - 1) * 40000000) by lia.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_solve_entail_wit_21_4 : solve_entail_wit_21_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH38 right ltac:(lia)) as Hpos_right.
  pose proof (PreH38 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH39 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  assert (Hdiff_nonneg :
    0 <= Znth right pos_l 0 - Znth (right - 1) pos_l 0) by lia.
  assert (Hdiff_le :
    Znth right pos_l 0 - Znth (right - 1) pos_l 0 <= 8000) by lia.
  assert (Hremain_nonneg :
    0 <= total - (Znth right prefix_l 0 - Znth left prefix_l 0)) by lia.
  pose proof (Z.mul_le_mono_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0) 8000
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) 5000
    Hdiff_nonneg Hdiff_le Hremain_nonneg PreH10) as Hproduct_le.
  pose proof (Z.mul_nonneg_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0)
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0))
    Hdiff_nonneg Hremain_nonneg) as Hproduct_nonneg.
  assert (Hcandidate_nonneg :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0))) by lia.
  assert (Hcandidate_le :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) <=
    (len - 1) * 40000000) by lia.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_solve_entail_wit_21_5 : solve_entail_wit_21_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH34 right ltac:(lia)) as Hpos_right.
  pose proof (PreH34 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH35 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  Left.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia.
Qed.

Lemma proof_of_solve_entail_wit_21_6 : solve_entail_wit_21_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH34 right ltac:(lia)) as Hpos_right.
  pose proof (PreH34 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH35 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  Left.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia.
Qed.

Lemma proof_of_solve_entail_wit_21_7 : solve_entail_wit_21_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH34 right ltac:(lia)) as Hpos_right.
  pose proof (PreH34 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH35 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia.
Qed.

Lemma proof_of_solve_entail_wit_21_8 : solve_entail_wit_21_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH34 right ltac:(lia)) as Hpos_right.
  pose proof (PreH34 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (PreH35 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia.
Qed.

Lemma proof_of_solve_entail_wit_22_1 : solve_entail_wit_22_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH50 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hold].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleftshape [Hrightshape Hintervals]].
  unfold StreetlightTableShape in Hleftshape, Hrightshape.
  destruct Hleftshape as [Hleft_table_len Hleft_row_len].
  destruct Hrightshape as [Hright_table_len Hright_row_len].
  assert (Hleft_index : 0 <= left < n_pre) by lia.
  assert (Hcell_index : 0 <= right - 1 < n_pre) by lia.
  pose proof (Hleft_row_len left Hleft_index) as Hleft_row_length.
  pose proof (Hright_row_len left Hleft_index) as Hright_row_length.
  Left.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT))
         (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by (rewrite Hright_row_length; lia).
      change
        (IntArray.full
           (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by
          (rewrite Hright_table_len; lia).
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT))
             (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (rewrite Hleft_row_length; lia).
           change
             (IntArray.full
                (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by
                (rewrite Hleft_table_len; lia).
              cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_2 : solve_entail_wit_22_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH50 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hold].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleftshape [Hrightshape Hintervals]].
  unfold StreetlightTableShape in Hleftshape, Hrightshape.
  destruct Hleftshape as [Hleft_table_len Hleft_row_len].
  destruct Hrightshape as [Hright_table_len Hright_row_len].
  assert (Hleft_index : 0 <= left < n_pre) by lia.
  assert (Hcell_index : 0 <= right - 1 < n_pre) by lia.
  pose proof (Hleft_row_len left Hleft_index) as Hleft_row_length.
  pose proof (Hright_row_len left Hleft_index) as Hright_row_length.
  Left.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT))
         (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by (rewrite Hright_row_length; lia).
      change
        (IntArray.full
           (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by
          (rewrite Hright_table_len; lia).
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT))
             (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (rewrite Hleft_row_length; lia).
           change
             (IntArray.full
                (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by
                (rewrite Hleft_table_len; lia).
              cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_3 : solve_entail_wit_22_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH50 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hold].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleftshape [Hrightshape Hintervals]].
  unfold StreetlightTableShape in Hleftshape, Hrightshape.
  destruct Hleftshape as [Hleft_table_len Hleft_row_len].
  destruct Hrightshape as [Hright_table_len Hright_row_len].
  assert (Hleft_index : 0 <= left < n_pre) by lia.
  assert (Hcell_index : 0 <= right - 1 < n_pre) by lia.
  pose proof (Hleft_row_len left Hleft_index) as Hleft_row_length.
  pose proof (Hright_row_len left Hleft_index) as Hright_row_length.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT))
         (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by (rewrite Hright_row_length; lia).
      change
        (IntArray.full
           (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by
          (rewrite Hright_table_len; lia).
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT))
             (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (rewrite Hleft_row_length; lia).
           change
             (IntArray.full
                (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by
                (rewrite Hleft_table_len; lia).
              cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_4 : solve_entail_wit_22_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH50 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hold].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleftshape [Hrightshape Hintervals]].
  unfold StreetlightTableShape in Hleftshape, Hrightshape.
  destruct Hleftshape as [Hleft_table_len Hleft_row_len].
  destruct Hrightshape as [Hright_table_len Hright_row_len].
  assert (Hleft_index : 0 <= left < n_pre) by lia.
  assert (Hcell_index : 0 <= right - 1 < n_pre) by lia.
  pose proof (Hleft_row_len left Hleft_index) as Hleft_row_length.
  pose proof (Hright_row_len left Hleft_index) as Hright_row_length.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT))
         (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by (rewrite Hright_row_length; lia).
      change
        (IntArray.full
           (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by
          (rewrite Hright_table_len; lia).
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT))
             (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (rewrite Hleft_row_length; lia).
           change
             (IntArray.full
                (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by
                (rewrite Hleft_table_len; lia).
              cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_5 : solve_entail_wit_22_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH46 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hold].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleftshape [Hrightshape Hintervals]].
  unfold StreetlightTableShape in Hleftshape, Hrightshape.
  destruct Hleftshape as [Hleft_table_len Hleft_row_len].
  destruct Hrightshape as [Hright_table_len Hright_row_len].
  assert (Hleft_index : 0 <= left < n_pre) by lia.
  assert (Hcell_index : 0 <= right - 1 < n_pre) by lia.
  pose proof (Hleft_row_len left Hleft_index) as Hleft_row_length.
  pose proof (Hright_row_len left Hleft_index) as Hright_row_length.
  Left.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT))
         (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by (rewrite Hright_row_length; lia).
      change
        (IntArray.full
           (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by
          (rewrite Hright_table_len; lia).
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT))
             (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (rewrite Hleft_row_length; lia).
           change
             (IntArray.full
                (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by
                (rewrite Hleft_table_len; lia).
              cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_6 : solve_entail_wit_22_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH46 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths Hprocessed].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_len Hleft_row_len].
  destruct Hright_shape as [Hright_len Hright_row_len].
  Left. Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1)
            (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
               (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_7 : solve_entail_wit_22_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH46 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths Hprocessed].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_len Hleft_row_len].
  destruct Hright_shape as [Hright_len Hright_row_len].
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1)
            (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
               (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_8 : solve_entail_wit_22_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH46 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths Hprocessed].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_len Hleft_row_len].
  destruct Hright_shape as [Hright_len Hright_row_len].
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1)
            (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
               (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_9 : solve_entail_wit_22_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH50 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths Hprocessed].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_len Hleft_row_len].
  destruct Hright_shape as [Hright_len Hright_row_len].
  Left. Left. Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1)
            (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
               (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_10 : solve_entail_wit_22_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH50 as Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hentry].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths Hprocessed].
  unfold StreetlightLengthsDone in Hlengths.
  destruct Hlengths as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_len Hleft_row_len].
  destruct Hright_shape as [Hright_len Hright_row_len].
  Left. Left. Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1)
            (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
          with
          (dp_l_pre + left * n_pre * sizeof (INT) +
           (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1)
                (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
               (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_11 : solve_entail_wit_22_11.
Proof.
  LLM_pre_process ltac:(lia).
  Left. Left. Right.
  pose proof PreH50 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
      (dp_r_pre + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
          (dp_l_pre + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try solve [auto].
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_12 : solve_entail_wit_22_12.
Proof.
  LLM_pre_process ltac:(lia).
  Left. Left. Right.
  pose proof PreH50 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
      (dp_r_pre + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
          (dp_l_pre + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try solve [auto].
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_13 : solve_entail_wit_22_13.
Proof.
  LLM_pre_process ltac:(lia).
  Left.
  pose proof PreH45 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
      (dp_r_pre + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
          (dp_l_pre + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try solve [auto].
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_14 : solve_entail_wit_22_14.
Proof.
  LLM_pre_process ltac:(lia).
  Left.
  pose proof PreH45 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
      (dp_r_pre + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
          (dp_l_pre + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try solve [auto].
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_15 : solve_entail_wit_22_15.
Proof.
  LLM_pre_process ltac:(lia).
  Right.
  pose proof PreH45 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
      (dp_r_pre + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial. lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT)) with
          (dp_l_pre + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial. lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr dp_l_pre n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                dp_l_pre left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial. lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    all: try solve [auto].
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_22_16 : solve_entail_wit_22_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left right_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_r_pre n_pre left) n_pre
         (Znth left right_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_r_pre left n_pre n_pre right_table
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    replace
      (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_l_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
         (Znth left left_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left left_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_l_pre n_pre left) n_pre
         (Znth left left_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_l_pre left n_pre n_pre left_table
         (Znth left left_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [auto | lia].
Qed.

Lemma proof_of_solve_entail_wit_22_17 : solve_entail_wit_22_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left right_table __default__List_Z) 0)).
  prop_apply_p
    (store_int_range
       (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)).
  Intros_p Hright_range.
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  assert (Hright_inf :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 = inf)
    by lia.
  assert (Hleft_inf :
    Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0 = inf)
    by lia.
  Left.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left right_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_r_pre n_pre left) n_pre
         (Znth left right_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_r_pre left n_pre n_pre right_table
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    replace
      (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_l_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left left_table_2 __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_l_pre n_pre left) n_pre
         (Znth left left_table_2 __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_l_pre left n_pre n_pre left_table_2
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_18 : solve_entail_wit_22_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left right_table __default__List_Z) 0)).
  prop_apply_p
    (store_int_range
       (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)).
  Intros_p Hright_range.
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  assert (Hright_inf :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 = inf)
    by lia.
  assert (Hleft_inf :
    Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0 = inf)
    by lia.
  Left.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left right_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_r_pre n_pre left) n_pre
         (Znth left right_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_r_pre left n_pre n_pre right_table
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    replace
      (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_l_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left left_table_2 __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_l_pre n_pre left) n_pre
         (Znth left left_table_2 __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_l_pre left n_pre n_pre left_table_2
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_19 : solve_entail_wit_22_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left right_table __default__List_Z) 0)).
  prop_apply_p
    (store_int_range
       (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)).
  Intros_p Hright_range.
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  assert (Hright_inf :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 = inf)
    by lia.
  assert (Hleft_inf :
    Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0 = inf)
    by lia.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left right_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_r_pre n_pre left) n_pre
         (Znth left right_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_r_pre left n_pre n_pre right_table
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    replace
      (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_l_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left left_table_2 __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_l_pre n_pre left) n_pre
         (Znth left left_table_2 __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_l_pre left n_pre n_pre left_table_2
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_22_20 : solve_entail_wit_22_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (store_int_range
       (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left right_table __default__List_Z) 0)).
  prop_apply_p
    (store_int_range
       (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)).
  Intros_p Hright_range.
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  assert (Hright_inf :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 = inf)
    by lia.
  assert (Hleft_inf :
    Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0 = inf)
    by lia.
  Right.
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - replace
      (dp_r_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left right_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_r_pre n_pre left) n_pre
         (Znth left right_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_r_pre left n_pre n_pre right_table
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    replace
      (dp_l_pre + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      (dp_l_pre + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_l_pre + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         (dp_l_pre + left * n_pre * sizeof (INT)) n_pre
         (Znth left left_table_2 __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_l_pre n_pre left) n_pre
         (Znth left left_table_2 __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         dp_l_pre left n_pre n_pre left_table_2
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial. lia. }
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solve_entail_wit_23_1 : solve_entail_wit_23_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_positions_order__right_close_a
      pos_l n_pre PreH34 PreH37) as Hmono.
  pose proof PreH42 as Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [Hprefix_length Hprefix_values].
  pose proof (Hprefix_values n_pre ltac:(lia)) as Htotal_sum.
  rewrite (sublist_self power_l n_pre ltac:(lia)) in Htotal_sum.
  assert (Hsum : sum power_l <= 5000) by lia.
  assert (Hsub : forall lo hi,
    0 <= lo <= hi -> hi <= n_pre ->
    0 <= sum (sublist lo hi power_l)).
  {
    intros lo hi Hlohi Hhi.
    eapply streetlight_sublist_sum_nonnegative__right_close_a; eauto.
  }
  pose proof
    (streetlight_close_interval_right__right_close_a
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      inf __default__List_Z PreH34 PreH5 PreH36 Hmono Hsum Hsub PreH10
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH1 PreH23 PreH24 PreH43)
    as Hfalse.
  contradiction.
Qed.

Lemma proof_of_solve_entail_wit_23_2 : solve_entail_wit_23_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_positions_order__right_close_a
      pos_l n_pre PreH34 PreH37) as Hmono.
  pose proof PreH42 as Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [Hprefix_length Hprefix_values].
  pose proof (Hprefix_values n_pre ltac:(lia)) as Htotal_sum.
  rewrite (sublist_self power_l n_pre ltac:(lia)) in Htotal_sum.
  assert (Hsum : sum power_l <= 5000) by lia.
  assert (Hsub : forall lo hi,
    0 <= lo <= hi -> hi <= n_pre ->
    0 <= sum (sublist lo hi power_l)).
  {
    intros lo hi Hlohi Hhi.
    eapply streetlight_sublist_sum_nonnegative__right_close_a; eauto.
  }
  pose proof
    (streetlight_close_interval_right__right_close_a
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      inf __default__List_Z PreH34 PreH5 PreH36 Hmono Hsum Hsub PreH10
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH1 PreH23 PreH24 PreH43)
    as Hfalse.
  contradiction.
Qed.

Lemma proof_of_solve_entail_wit_23_3 : solve_entail_wit_23_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_positions_order__right_close_a
      pos_l n_pre PreH34 PreH37) as Hmono.
  pose proof PreH42 as Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [Hprefix_length Hprefix_values].
  pose proof (Hprefix_values n_pre ltac:(lia)) as Htotal_sum.
  rewrite (sublist_self power_l n_pre ltac:(lia)) in Htotal_sum.
  assert (Hsum : sum power_l <= 5000) by lia.
  assert (Hsub : forall lo hi,
    0 <= lo <= hi -> hi <= n_pre ->
    0 <= sum (sublist lo hi power_l)).
  {
    intros lo hi Hlohi Hhi.
    eapply streetlight_sublist_sum_nonnegative__right_close_a; eauto.
  }
  pose proof
    (streetlight_close_interval_right__right_close_a
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      inf __default__List_Z PreH34 PreH5 PreH36 Hmono Hsum Hsub PreH10
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH1 PreH23 PreH24 PreH43)
    as Hfalse.
  contradiction.
Qed.

Lemma proof_of_solve_entail_wit_23_4 : solve_entail_wit_23_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_positions_order__right_close_a
      pos_l n_pre PreH34 PreH37) as Hmono.
  pose proof PreH42 as Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [Hprefix_length Hprefix_values].
  pose proof (Hprefix_values n_pre ltac:(lia)) as Htotal_sum.
  rewrite (sublist_self power_l n_pre ltac:(lia)) in Htotal_sum.
  assert (Hsum : sum power_l <= 5000) by lia.
  assert (Hsub : forall lo hi,
    0 <= lo <= hi -> hi <= n_pre ->
    0 <= sum (sublist lo hi power_l)).
  {
    intros lo hi Hlohi Hhi.
    eapply streetlight_sublist_sum_nonnegative__right_close_a; eauto.
  }
  pose proof
    (streetlight_close_interval_right__right_close_a
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      inf __default__List_Z PreH34 PreH5 PreH36 Hmono Hsum Hsub PreH10
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH1 PreH23 PreH24 PreH43)
    as Hfalse.
  contradiction.
Qed.

Lemma proof_of_solve_entail_wit_23_5 : solve_entail_wit_23_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  set (right_row :=
    replace_Znth right best
      (Znth left right_table_2 __default__List_Z)).
  set (right_table := replace_Znth left right_row right_table_2).
  assert (Hminimum :
    StreetlightEndpointMinimum pos_l power_l start left right right best).
  {
    eapply
      (streetlight_right_endpoint_minimum__right_close_b
        pos_l power_l prefix_l_2 left_table_2 right_table_2
        n_pre start len left right remain best inf __default__List_Z).
    - exact PreH1.
    - exact PreH4.
    - exact PreH5.
    - exact PreH10.
    - exact PreH11.
    - exact PreH8.
    - exact PreH9.
    - exact PreH12.
    - exact PreH13.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH19.
    - exact PreH35.
    - exact PreH36.
    - exact PreH38.
    - rewrite <- PreH3. exact PreH21.
    - exact PreH43.
    - exact PreH44.
    - exact PreH23.
    - exact PreH25.
    - exact PreH26.
    - exact PreH27.
    - exact PreH28.
  }
  assert (Hnext :
    StreetlightLeftProgress pos_l power_l left_table_2 right_table
      n_pre start len (left + 1)).
  {
    unfold right_table, right_row.
    eapply streetlight_close_interval_and_advance__right_close_b.
    - exact PreH10.
    - exact PreH12.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH44.
    - exact Hminimum.
  }
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hdone_shape _].
  unfold StreetlightLengthsDone in Hdone_shape.
  destruct Hdone_shape as [_ [Hright_shape _]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table_2) by lia.
  assert (Hrow_length_default :
    Zlength (Znth left right_table_2 __default__List_Z) = n_pre).
  {
    rewrite
      (Znth_indep right_table_2 left __default__List_Z (@nil Z)
        Hleft_index).
    apply Hrow_length; lia.
  }
  assert (Hpending :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending_left.
    unfold right_table, right_row.
    destruct (Z.eq_dec pending_left left) as [Heq | Hneq].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrow_length_default; try lia).
      apply PreH42; exact Hpending_left.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia; exact Hneq).
      apply PreH42; exact Hpending_left.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold right_row.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre left n_pre n_pre right_table_2 right_row ltac:(lia))
        as Hmerge.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre left) n_pre right_row)
        with
        (IntArray.full
          (dp_r_pre + left * n_pre * sizeof (INT)) n_pre right_row)
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      fold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_6 : solve_entail_wit_23_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  set (right_row :=
    replace_Znth right best
      (Znth left right_table_2 __default__List_Z)).
  set (right_table := replace_Znth left right_row right_table_2).
  assert (Hminimum :
    StreetlightEndpointMinimum pos_l power_l start left right right best).
  {
    eapply
      (streetlight_right_endpoint_minimum__right_close_b
        pos_l power_l prefix_l_2 left_table_2 right_table_2
        n_pre start len left right remain best inf __default__List_Z).
    - exact PreH1.
    - exact PreH4.
    - exact PreH5.
    - exact PreH10.
    - exact PreH11.
    - exact PreH8.
    - exact PreH9.
    - exact PreH12.
    - exact PreH13.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH19.
    - exact PreH35.
    - exact PreH36.
    - exact PreH38.
    - rewrite <- PreH3. exact PreH21.
    - exact PreH43.
    - exact PreH44.
    - exact PreH23.
    - exact PreH25.
    - exact PreH26.
    - exact PreH27.
    - exact PreH28.
  }
  assert (Hnext :
    StreetlightLeftProgress pos_l power_l left_table_2 right_table
      n_pre start len (left + 1)).
  {
    unfold right_table, right_row.
    eapply streetlight_close_interval_and_advance__right_close_b.
    - exact PreH10.
    - exact PreH12.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH44.
    - exact Hminimum.
  }
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hdone_shape _].
  unfold StreetlightLengthsDone in Hdone_shape.
  destruct Hdone_shape as [_ [Hright_shape _]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table_2) by lia.
  assert (Hrow_length_default :
    Zlength (Znth left right_table_2 __default__List_Z) = n_pre).
  {
    rewrite
      (Znth_indep right_table_2 left __default__List_Z (@nil Z)
        Hleft_index).
    apply Hrow_length; lia.
  }
  assert (Hpending :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending_left.
    unfold right_table, right_row.
    destruct (Z.eq_dec pending_left left) as [Heq | Hneq].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrow_length_default; try lia).
      apply PreH42; exact Hpending_left.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia; exact Hneq).
      apply PreH42; exact Hpending_left.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold right_row.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre left n_pre n_pre right_table_2 right_row ltac:(lia))
        as Hmerge.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre left) n_pre right_row)
        with
        (IntArray.full
          (dp_r_pre + left * n_pre * sizeof (INT)) n_pre right_row)
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      fold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_7 : solve_entail_wit_23_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  set (right_row :=
    replace_Znth right best
      (Znth left right_table_2 __default__List_Z)).
  set (right_table := replace_Znth left right_row right_table_2).
  assert (Hminimum :
    StreetlightEndpointMinimum pos_l power_l start left right right best).
  {
    eapply
      (streetlight_right_endpoint_minimum__right_close_b
        pos_l power_l prefix_l_2 left_table_2 right_table_2
        n_pre start len left right remain best inf __default__List_Z).
    - exact PreH1.
    - exact PreH4.
    - exact PreH5.
    - exact PreH10.
    - exact PreH11.
    - exact PreH8.
    - exact PreH9.
    - exact PreH12.
    - exact PreH13.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH19.
    - exact PreH35.
    - exact PreH36.
    - exact PreH38.
    - rewrite <- PreH3. exact PreH21.
    - exact PreH43.
    - exact PreH44.
    - exact PreH23.
    - exact PreH25.
    - exact PreH26.
    - exact PreH27.
    - exact PreH28.
  }
  assert (Hnext :
    StreetlightLeftProgress pos_l power_l left_table_2 right_table
      n_pre start len (left + 1)).
  {
    unfold right_table, right_row.
    eapply streetlight_close_interval_and_advance__right_close_b.
    - exact PreH10.
    - exact PreH12.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH44.
    - exact Hminimum.
  }
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hdone_shape _].
  unfold StreetlightLengthsDone in Hdone_shape.
  destruct Hdone_shape as [_ [Hright_shape _]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table_2) by lia.
  assert (Hrow_length_default :
    Zlength (Znth left right_table_2 __default__List_Z) = n_pre).
  {
    rewrite
      (Znth_indep right_table_2 left __default__List_Z (@nil Z)
        Hleft_index).
    apply Hrow_length; lia.
  }
  assert (Hpending :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending_left.
    unfold right_table, right_row.
    destruct (Z.eq_dec pending_left left) as [Heq | Hneq].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrow_length_default; try lia).
      apply PreH42; exact Hpending_left.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia; exact Hneq).
      apply PreH42; exact Hpending_left.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold right_row.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre left n_pre n_pre right_table_2 right_row ltac:(lia))
        as Hmerge.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre left) n_pre right_row)
        with
        (IntArray.full
          (dp_r_pre + left * n_pre * sizeof (INT)) n_pre right_row)
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      fold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_8 : solve_entail_wit_23_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  set (right_row :=
    replace_Znth right best
      (Znth left right_table_2 __default__List_Z)).
  set (right_table := replace_Znth left right_row right_table_2).
  assert (Hminimum :
    StreetlightEndpointMinimum pos_l power_l start left right right best).
  {
    eapply
      (streetlight_right_endpoint_minimum__right_close_b
        pos_l power_l prefix_l_2 left_table_2 right_table_2
        n_pre start len left right remain best inf __default__List_Z).
    - exact PreH1.
    - exact PreH4.
    - exact PreH5.
    - exact PreH10.
    - exact PreH11.
    - exact PreH8.
    - exact PreH9.
    - exact PreH12.
    - exact PreH13.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH19.
    - exact PreH35.
    - exact PreH36.
    - exact PreH38.
    - rewrite <- PreH3. exact PreH21.
    - exact PreH43.
    - exact PreH44.
    - exact PreH23.
    - exact PreH25.
    - exact PreH26.
    - exact PreH27.
    - exact PreH28.
  }
  assert (Hnext :
    StreetlightLeftProgress pos_l power_l left_table_2 right_table
      n_pre start len (left + 1)).
  {
    unfold right_table, right_row.
    eapply streetlight_close_interval_and_advance__right_close_b.
    - exact PreH10.
    - exact PreH12.
    - exact PreH14.
    - exact PreH15.
    - exact PreH16.
    - exact PreH44.
    - exact Hminimum.
  }
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hdone_shape _].
  unfold StreetlightLengthsDone in Hdone_shape.
  destruct Hdone_shape as [_ [Hright_shape _]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table_2) by lia.
  assert (Hrow_length_default :
    Zlength (Znth left right_table_2 __default__List_Z) = n_pre).
  {
    rewrite
      (Znth_indep right_table_2 left __default__List_Z (@nil Z)
        Hleft_index).
    apply Hrow_length; lia.
  }
  assert (Hpending :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending_left.
    unfold right_table, right_row.
    destruct (Z.eq_dec pending_left left) as [Heq | Hneq].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrow_length_default; try lia).
      apply PreH42; exact Hpending_left.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia; exact Hneq).
      apply PreH42; exact Hpending_left.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with
      (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + fold right_row.
      pose proof
        (IntArray2.missing_i_merge_to_full
          dp_r_pre left n_pre n_pre right_table_2 right_row ltac:(lia))
        as Hmerge.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_r_pre n_pre left) n_pre right_row)
        with
        (IntArray.full
          (dp_r_pre + left * n_pre * sizeof (INT)) n_pre right_row)
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      fold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_9 : solve_entail_wit_23_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  cbn in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths_shape _].
  unfold StreetlightLengthsDone in Hlengths_shape.
  destruct Hlengths_shape as
    [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_length].
  destruct Hright_shape as [Hright_table_length Hright_row_length].
  assert (Hleft_index_left : 0 <= left < Zlength left_table_2) by
    (rewrite Hleft_table_length; lia).
  assert (Hleft_index_right : 0 <= left < Zlength right_table_2) by
    (rewrite Hright_table_length; lia).
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table_2 __default__List_Z)).
  {
    rewrite (Znth_indep right_table_2 left __default__List_Z (@nil Z)
               Hleft_index_right).
    rewrite Hright_row_length by lia.
    lia.
  }
  pose proof
    (Znth_indep left_table_2 left __default__List_Z (@nil Z)
       Hleft_index_left) as Hleft_default.
  pose proof
    (Znth_indep right_table_2 left __default__List_Z (@nil Z)
       Hleft_index_right) as Hright_default.
  pose proof PreH43 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_value].
  assert (Htotal_sum : sum power_l = total).
  {
    rewrite PreH3.
    rewrite Hprefix_value by lia.
    rewrite (sublist_self power_l n_pre) by lia.
    reflexivity.
  }
  assert (Hinterval_sum :
    Znth right prefix_l_2 0 - Znth left prefix_l_2 0 =
      sum (sublist left right power_l)).
  {
    rewrite Hprefix_value by lia.
    rewrite Hprefix_value by lia.
    rewrite (sublist_split 0 right left power_l) by lia.
    rewrite sum_app.
    lia.
  }
  assert (Hremaining :
    remain = sum power_l - sum (sublist left right power_l)) by lia.
  assert (Hminimum :
    StreetlightEndpointMinimum
      pos_l power_l start left right right best).
  {
    eapply
      (streetlight_close_endpoint_right__right_close_c
         pos_l power_l left_table_2 right_table_2 n_pre start len left right
         inf remain best).
    - exact PreH1.
    - exact PreH5.
    - exact PreH35.
    - exact PreH36.
    - exact PreH37.
    - exact PreH39.
    - lia.
    - exact PreH10.
    - exact PreH12.
    - lia.
    - exact PreH16.
    - exact PreH14.
    - exact Hremaining.
    - rewrite <- Hright_default. exact PreH23.
    - rewrite <- Hright_default. exact PreH26.
    - rewrite <- Hleft_default. exact PreH27.
    - rewrite <- Hright_default. exact PreH28.
    - exact PreH44.
  }
  set (right_table :=
    replace_Znth left
      (replace_Znth right best
         (Znth left right_table_2 __default__List_Z))
      right_table_2).
  assert (Hnext :
    StreetlightLeftProgress
      pos_l power_l left_table_2 right_table n_pre start len (left + 1)).
  {
    unfold right_table.
    rewrite Hright_default.
    eapply streetlight_close_interval_right__right_close_c;
      eauto; lia.
  }
  assert (Hpending_left :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending.
    unfold right_table.
    destruct (Z.eq_dec pending_left left) as [Hsame | Hdiff].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index_right.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_row_length by lia; lia).
      apply PreH42. lia.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_table_length; try lia; exact Hdiff).
      apply PreH42. exact Hpending.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table_2
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        with
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_10 : solve_entail_wit_23_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  cbn in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths_shape _].
  unfold StreetlightLengthsDone in Hlengths_shape.
  destruct Hlengths_shape as
    [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_length].
  destruct Hright_shape as [Hright_table_length Hright_row_length].
  assert (Hleft_index_left : 0 <= left < Zlength left_table_2) by
    (rewrite Hleft_table_length; lia).
  assert (Hleft_index_right : 0 <= left < Zlength right_table_2) by
    (rewrite Hright_table_length; lia).
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table_2 __default__List_Z)).
  {
    rewrite (Znth_indep right_table_2 left __default__List_Z (@nil Z)
               Hleft_index_right).
    rewrite Hright_row_length by lia.
    lia.
  }
  pose proof
    (Znth_indep left_table_2 left __default__List_Z (@nil Z)
       Hleft_index_left) as Hleft_default.
  pose proof
    (Znth_indep right_table_2 left __default__List_Z (@nil Z)
       Hleft_index_right) as Hright_default.
  pose proof PreH43 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_value].
  assert (Htotal_sum : sum power_l = total).
  {
    rewrite PreH3.
    rewrite Hprefix_value by lia.
    rewrite (sublist_self power_l n_pre) by lia.
    reflexivity.
  }
  assert (Hinterval_sum :
    Znth right prefix_l_2 0 - Znth left prefix_l_2 0 =
      sum (sublist left right power_l)).
  {
    rewrite Hprefix_value by lia.
    rewrite Hprefix_value by lia.
    rewrite (sublist_split 0 right left power_l) by lia.
    rewrite sum_app.
    lia.
  }
  assert (Hremaining :
    remain = sum power_l - sum (sublist left right power_l)) by lia.
  assert (Hminimum :
    StreetlightEndpointMinimum
      pos_l power_l start left right right best).
  {
    eapply
      (streetlight_close_endpoint_right__right_close_c
         pos_l power_l left_table_2 right_table_2 n_pre start len left right
         inf remain best).
    - exact PreH1.
    - exact PreH5.
    - exact PreH35.
    - exact PreH36.
    - exact PreH37.
    - exact PreH39.
    - lia.
    - exact PreH10.
    - exact PreH12.
    - lia.
    - exact PreH16.
    - exact PreH14.
    - exact Hremaining.
    - rewrite <- Hright_default. exact PreH23.
    - rewrite <- Hright_default. exact PreH26.
    - rewrite <- Hleft_default. exact PreH27.
    - rewrite <- Hright_default. exact PreH28.
    - exact PreH44.
  }
  set (right_table :=
    replace_Znth left
      (replace_Znth right best
         (Znth left right_table_2 __default__List_Z))
      right_table_2).
  assert (Hnext :
    StreetlightLeftProgress
      pos_l power_l left_table_2 right_table n_pre start len (left + 1)).
  {
    unfold right_table.
    rewrite Hright_default.
    eapply streetlight_close_interval_right__right_close_c;
      eauto; lia.
  }
  assert (Hpending_left :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending.
    unfold right_table.
    destruct (Z.eq_dec pending_left left) as [Hsame | Hdiff].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index_right.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_row_length by lia; lia).
      apply PreH42. lia.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_table_length; try lia; exact Hdiff).
      apply PreH42. exact Hpending.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table_2
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        with
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_11 : solve_entail_wit_23_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  cbn in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths_shape _].
  unfold StreetlightLengthsDone in Hlengths_shape.
  destruct Hlengths_shape as
    [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_length].
  destruct Hright_shape as [Hright_table_length Hright_row_length].
  assert (Hleft_index_left : 0 <= left < Zlength left_table_2) by
    (rewrite Hleft_table_length; lia).
  assert (Hleft_index_right : 0 <= left < Zlength right_table_2) by
    (rewrite Hright_table_length; lia).
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table_2 __default__List_Z)).
  {
    rewrite (Znth_indep right_table_2 left __default__List_Z (@nil Z)
               Hleft_index_right).
    rewrite Hright_row_length by lia.
    lia.
  }
  pose proof
    (Znth_indep left_table_2 left __default__List_Z (@nil Z)
       Hleft_index_left) as Hleft_default.
  pose proof
    (Znth_indep right_table_2 left __default__List_Z (@nil Z)
       Hleft_index_right) as Hright_default.
  pose proof PreH43 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_value].
  assert (Htotal_sum : sum power_l = total).
  {
    rewrite PreH3.
    rewrite Hprefix_value by lia.
    rewrite (sublist_self power_l n_pre) by lia.
    reflexivity.
  }
  assert (Hinterval_sum :
    Znth right prefix_l_2 0 - Znth left prefix_l_2 0 =
      sum (sublist left right power_l)).
  {
    rewrite Hprefix_value by lia.
    rewrite Hprefix_value by lia.
    rewrite (sublist_split 0 right left power_l) by lia.
    rewrite sum_app.
    lia.
  }
  assert (Hremaining :
    remain = sum power_l - sum (sublist left right power_l)) by lia.
  assert (Hminimum :
    StreetlightEndpointMinimum
      pos_l power_l start left right right best).
  {
    eapply
      (streetlight_close_endpoint_right__right_close_c
         pos_l power_l left_table_2 right_table_2 n_pre start len left right
         inf remain best).
    - exact PreH1.
    - exact PreH5.
    - exact PreH35.
    - exact PreH36.
    - exact PreH37.
    - exact PreH39.
    - lia.
    - exact PreH10.
    - exact PreH12.
    - lia.
    - exact PreH16.
    - exact PreH14.
    - exact Hremaining.
    - rewrite <- Hright_default. exact PreH23.
    - rewrite <- Hright_default. exact PreH26.
    - rewrite <- Hleft_default. exact PreH27.
    - rewrite <- Hright_default. exact PreH28.
    - exact PreH44.
  }
  set (right_table :=
    replace_Znth left
      (replace_Znth right best
         (Znth left right_table_2 __default__List_Z))
      right_table_2).
  assert (Hnext :
    StreetlightLeftProgress
      pos_l power_l left_table_2 right_table n_pre start len (left + 1)).
  {
    unfold right_table.
    rewrite Hright_default.
    eapply streetlight_close_interval_right__right_close_c;
      eauto; lia.
  }
  assert (Hpending_left :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending.
    unfold right_table.
    destruct (Z.eq_dec pending_left left) as [Hsame | Hdiff].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index_right.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_row_length by lia; lia).
      apply PreH42. lia.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_table_length; try lia; exact Hdiff).
      apply PreH42. exact Hpending.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table_2
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        with
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_12 : solve_entail_wit_23_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  pose proof PreH44 as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  cbn in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths_shape _].
  unfold StreetlightLengthsDone in Hlengths_shape.
  destruct Hlengths_shape as
    [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_length].
  destruct Hright_shape as [Hright_table_length Hright_row_length].
  assert (Hleft_index_left : 0 <= left < Zlength left_table_2) by
    (rewrite Hleft_table_length; lia).
  assert (Hleft_index_right : 0 <= left < Zlength right_table_2) by
    (rewrite Hright_table_length; lia).
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table_2 __default__List_Z)).
  {
    rewrite (Znth_indep right_table_2 left __default__List_Z (@nil Z)
               Hleft_index_right).
    rewrite Hright_row_length by lia.
    lia.
  }
  pose proof
    (Znth_indep left_table_2 left __default__List_Z (@nil Z)
       Hleft_index_left) as Hleft_default.
  pose proof
    (Znth_indep right_table_2 left __default__List_Z (@nil Z)
       Hleft_index_right) as Hright_default.
  pose proof PreH43 as Hprefix_progress.
  unfold StreetlightPrefixProgress in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_value].
  assert (Htotal_sum : sum power_l = total).
  {
    rewrite PreH3.
    rewrite Hprefix_value by lia.
    rewrite (sublist_self power_l n_pre) by lia.
    reflexivity.
  }
  assert (Hinterval_sum :
    Znth right prefix_l_2 0 - Znth left prefix_l_2 0 =
      sum (sublist left right power_l)).
  {
    rewrite Hprefix_value by lia.
    rewrite Hprefix_value by lia.
    rewrite (sublist_split 0 right left power_l) by lia.
    rewrite sum_app.
    lia.
  }
  assert (Hremaining :
    remain = sum power_l - sum (sublist left right power_l)) by lia.
  assert (Hminimum :
    StreetlightEndpointMinimum
      pos_l power_l start left right right best).
  {
    eapply
      (streetlight_close_endpoint_right__right_close_c
         pos_l power_l left_table_2 right_table_2 n_pre start len left right
         inf remain best).
    - exact PreH1.
    - exact PreH5.
    - exact PreH35.
    - exact PreH36.
    - exact PreH37.
    - exact PreH39.
    - lia.
    - exact PreH10.
    - exact PreH12.
    - lia.
    - exact PreH16.
    - exact PreH14.
    - exact Hremaining.
    - rewrite <- Hright_default. exact PreH23.
    - rewrite <- Hright_default. exact PreH26.
    - rewrite <- Hleft_default. exact PreH27.
    - rewrite <- Hright_default. exact PreH28.
    - exact PreH44.
  }
  set (right_table :=
    replace_Znth left
      (replace_Znth right best
         (Znth left right_table_2 __default__List_Z))
      right_table_2).
  assert (Hnext :
    StreetlightLeftProgress
      pos_l power_l left_table_2 right_table n_pre start len (left + 1)).
  {
    unfold right_table.
    rewrite Hright_default.
    eapply streetlight_close_interval_right__right_close_c;
      eauto; lia.
  }
  assert (Hpending_left :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending.
    unfold right_table.
    destruct (Z.eq_dec pending_left left) as [Hsame | Hdiff].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index_right.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_row_length by lia; lia).
      apply PreH42. lia.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_table_length; try lia; exact Hdiff).
      apply PreH42. exact Hpending.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - replace (dp_r_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_r_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_r_pre + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial. lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           dp_r_pre left n_pre n_pre right_table_2
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_r_pre n_pre left) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        with
        (IntArray.full (dp_r_pre + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solve_entail_wit_23_13 : solve_entail_wit_23_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_close_interval_right__right_close_d
      pos_l power_l left_table_2 right_table_2 __default__List_Z
      n_pre start len left right inf PreH2 PreH11 PreH13 PreH14 PreH15
      PreH16 PreH1 PreH17 PreH35 PreH37)
    as Hprogress.
  Left.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solve_entail_wit_23_14 : solve_entail_wit_23_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_close_interval_right__right_close_d
      pos_l power_l left_table_2 right_table_2 __default__List_Z
      n_pre start len left right inf PreH2 PreH11 PreH13 PreH14 PreH15
      PreH16 PreH1 PreH17 PreH35 PreH37)
    as Hprogress.
  Left.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solve_entail_wit_23_15 : solve_entail_wit_23_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_close_interval_right__right_close_d
      pos_l power_l left_table_2 right_table_2 __default__List_Z
      n_pre start len left right inf PreH2 PreH11 PreH13 PreH14 PreH15
      PreH16 PreH1 PreH17 PreH35 PreH37)
    as Hprogress.
  Right.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solve_entail_wit_23_16 : solve_entail_wit_23_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (streetlight_close_interval_right__right_close_d
      pos_l power_l left_table_2 right_table_2 __default__List_Z
      n_pre start len left right inf PreH2 PreH11 PreH13 PreH14 PreH15
      PreH16 PreH1 PreH17 PreH35 PreH37)
    as Hprogress.
  Right.
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_1 : solve_entail_wit_24_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH3.
  eapply streetlight_lengths_done_succ__length_close_a.
  - exact PreH32.
  - intros query_left Hquery_left Hquery_right Hquery_contains.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_2 : solve_entail_wit_24_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH30.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_3 : solve_entail_wit_24_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_4 : solve_entail_wit_24_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH28.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_5 : solve_entail_wit_24_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH27.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_6 : solve_entail_wit_24_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_1_split_goal_7 : solve_entail_wit_24_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH25.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_1 : solve_entail_wit_24_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_24_1_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_1 : solve_entail_wit_24_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH3.
  eapply streetlight_lengths_done_succ__length_close_a.
  - exact PreH32.
  - intros query_left Hquery_left Hquery_right Hquery_contains.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_2 : solve_entail_wit_24_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH30.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_3 : solve_entail_wit_24_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH29.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_4 : solve_entail_wit_24_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH28.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_5 : solve_entail_wit_24_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH27.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_6 : solve_entail_wit_24_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_2_split_goal_7 : solve_entail_wit_24_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH25.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_2 : solve_entail_wit_24_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_24_2_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_1 : solve_entail_wit_24_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH3.
  eapply streetlight_lengths_done_succ__length_close_b.
  - exact PreH32.
  - intros query_left Hquery_left Hquery_right Hquery_contains.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_2 : solve_entail_wit_24_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_3 : solve_entail_wit_24_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_4 : solve_entail_wit_24_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH28.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_5 : solve_entail_wit_24_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH27.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_6 : solve_entail_wit_24_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_3_split_goal_7 : solve_entail_wit_24_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH25.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_3 : solve_entail_wit_24_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_24_3_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_1 : solve_entail_wit_24_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH3.
  eapply streetlight_lengths_done_succ__length_close_b.
  - exact PreH32.
  - intros query_left Hquery_left Hquery_right Hquery_contains.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_2 : solve_entail_wit_24_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_3 : solve_entail_wit_24_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH29.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_4 : solve_entail_wit_24_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH28.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_5 : solve_entail_wit_24_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH27.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_6 : solve_entail_wit_24_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_24_4_split_goal_7 : solve_entail_wit_24_4_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH25.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_4 : solve_entail_wit_24_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_24_4_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_25 : solve_entail_wit_25.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpower_sum : sum power_l <= 5000).
  { unfold StreetlightPrefixProgress in PreH23.
    destruct PreH23 as [Hprefix_length Hprefix_values].
    specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  unfold StreetlightLengthsDone in PreH24.
  destruct PreH24 as [Hleft_shape [Hright_shape Hlengths_done]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_lengths].
  destruct Hright_shape as [Hright_table_length Hright_row_lengths].
  pose proof
    (Hlengths_done n_pre 0 (n_pre - 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Hfull_interval.
  unfold StreetlightIntervalCorrect in Hfull_interval.
  destruct Hfull_interval as [Hleft_entry Hright_entry].
  assert (Hleft_default :
    Znth 0 left_table __default__List_Z = Znth 0 left_table nil).
  { apply Znth_indep.
    lia. }
  assert (Hright_default :
    Znth 0 right_table __default__List_Z = Znth 0 right_table nil).
  { apply Znth_indep.
    lia. }
  rewrite <- Hleft_default in Hleft_entry.
  rewrite <- Hright_default in Hright_entry.
  pose proof
    (streetlight_final_candidates_cases__final_state
      pos_l power_l left_table right_table n_pre start
      (Znth (n_pre - 1) (Znth 0 left_table __default__List_Z) 0)
      (Znth (n_pre - 1) (Znth 0 right_table __default__List_Z) 0)
      PreH15 PreH16 ltac:(lia) ltac:(lia)
      PreH17 PreH18 PreH19 Hpower_sum Hleft_entry Hright_entry)
    as [Hfinal_candidates Hfinal_case].
  replace
    (dp_r_pre + (0 * n_pre + (n_pre - 1)) * sizeof(INT))
    with
    ((dp_r_pre + 0 * n_pre * sizeof(INT)) +
      (n_pre - 1) * sizeof(INT)) by ring.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full
      (dp_r_pre + 0 * n_pre * sizeof(INT)) (n_pre - 1) n_pre
      (Znth (n_pre - 1) (Znth 0 right_table __default__List_Z) 0)
      (Znth 0 right_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  match goal with
  | |- IntArray.full _ _ _ ** ?R |-- ?Q =>
      change
        (IntArray2.ElemArray.full (IntArray2.row_addr dp_r_pre n_pre 0)
          n_pre (Znth 0 right_table __default__List_Z) ** R |-- Q)
  end.
  sep_apply_l_atomic
    (IntArray2.missing_i_merge_to_full
      dp_r_pre 0 n_pre n_pre right_table
      (Znth 0 right_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  replace
    (dp_l_pre + (0 * n_pre + (n_pre - 1)) * sizeof(INT))
    with
    ((dp_l_pre + 0 * n_pre * sizeof(INT)) +
      (n_pre - 1) * sizeof(INT)) by ring.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full
      (dp_l_pre + 0 * n_pre * sizeof(INT)) (n_pre - 1) n_pre
      (Znth (n_pre - 1) (Znth 0 left_table __default__List_Z) 0)
      (Znth 0 left_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  match goal with
  | |- IntArray.full _ _ _ ** ?R |-- ?Q =>
      change
        (IntArray2.ElemArray.full (IntArray2.row_addr dp_l_pre n_pre 0)
          n_pre (Znth 0 left_table __default__List_Z) ** R |-- Q)
  end.
  sep_apply_l_atomic
    (IntArray2.missing_i_merge_to_full
      dp_l_pre 0 n_pre n_pre left_table
      (Znth 0 left_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  Ltac finish_final_case
      right_table_arg left_table_arg prefix_arg
      pos_addr_arg n_arg positions_arg
      power_addr_arg powers_arg prefix_addr_arg
      left_addr_arg right_addr_arg :=
    Exists right_table_arg;
    Exists left_table_arg;
    Exists prefix_arg;
    split_pure_spatial;
    [ cancel (IntArray.full pos_addr_arg n_arg positions_arg);
      cancel (IntArray.full power_addr_arg n_arg powers_arg);
      cancel (IntArray.full prefix_addr_arg (n_arg + 1) prefix_arg);
      cancel (IntArray2.full left_addr_arg n_arg n_arg left_table_arg);
      cancel (IntArray2.full right_addr_arg n_arg n_arg right_table_arg)
    | split_pures;
      dump_pre_spatial;
      first [assumption | lia] ].
  destruct Hfinal_case as
    [Hcase | [Hcase | [Hcase | Hcase]]].
  - destruct Hcase as
      [Hright_inf [Hleft_nonnegative [Hleft_bounded Hleft_finite]]].
    repeat Left.
    finish_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l pre_pre dp_l_pre dp_r_pre.
  - destruct Hcase as
      [Hleft_nonnegative
        [Hleft_bounded
          [Hright_nonnegative [Hright_bounded Hright_finite]]]].
    Left. Left. Right.
    finish_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l pre_pre dp_l_pre dp_r_pre.
  - destruct Hcase as
      [Hleft_nonnegative
        [Hleft_bounded
          [Hright_nonnegative [Hright_bounded Hleft_finite]]]].
    Left. Right.
    finish_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l pre_pre dp_l_pre dp_r_pre.
  - destruct Hcase as
      [Hleft_inf [Hright_nonnegative [Hright_bounded Hright_finite]]].
    Right.
    finish_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l pre_pre dp_l_pre dp_r_pre.
Qed.

Lemma proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightFinalCandidates in PreH20.
  destruct PreH20 as [_ [_ Hminimum]].
  rewrite Z.min_r in Hminimum by lia.
  subst start.
  exact Hminimum.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solve_return_wit_2_split_goal_1 : solve_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightFinalCandidates in PreH20.
  destruct PreH20 as [_ [_ Hminimum]].
  rewrite Z.min_r in Hminimum by lia.
  subst start.
  exact Hminimum.
Qed.

Lemma proof_of_solve_return_wit_2 : solve_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solve_return_wit_3_split_goal_1 : solve_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightFinalCandidates in PreH19.
  destruct PreH19 as [_ [_ Hminimum]].
  rewrite PreH3 in Hminimum.
  rewrite PreH15 in Hminimum.
  rewrite Z.min_r in Hminimum by lia.
  exact Hminimum.
Qed.

Lemma proof_of_solve_return_wit_3 : solve_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solve_return_wit_4_split_goal_1 : solve_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightFinalCandidates in PreH19.
  destruct PreH19 as [_ [_ Hminimum]].
  rewrite PreH3 in Hminimum.
  rewrite Z.min_l in Hminimum by lia.
  exact Hminimum.
Qed.

Lemma proof_of_solve_return_wit_4 : solve_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_solve_return_wit_5_split_goal_1 : solve_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightFinalCandidates in PreH20.
  destruct PreH20 as [_ [_ Hminimum]].
  rewrite PreH3 in Hminimum.
  rewrite Z.min_l in Hminimum by lia.
  exact Hminimum.
Qed.

Lemma proof_of_solve_return_wit_5 : solve_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_solve_return_wit_6_split_goal_1 : solve_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StreetlightFinalCandidates in PreH20.
  destruct PreH20 as [_ [_ Hminimum]].
  rewrite PreH3 in Hminimum.
  rewrite Z.min_l in Hminimum by lia.
  exact Hminimum.
Qed.

Lemma proof_of_solve_return_wit_6 : solve_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_return_wit_6_split_goal_1.
Qed.
