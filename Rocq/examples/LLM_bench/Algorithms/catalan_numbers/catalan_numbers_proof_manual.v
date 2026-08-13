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
From SimpleC.EE.LLM_bench.Algorithms.catalan_numbers Require Import catalan_numbers_goal.
From SimpleC.EE.LLM_bench.Algorithms.catalan_numbers Require Import catalan_numbers_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib.
Local Open Scope sac.

Lemma proof_of_id_return_wit_1_split_goal_1 : id_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_id_return_wit_1 : id_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_id_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_1 : solve_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval. subst retval_2.
  unfold StackRowProgress in PreH22.
  destruct PreH22 as [_ [_ Hprefix]].
  unfold StackTablePrefix in Hprefix.
  destruct Hprefix as [_ [_ Hcells]].
  assert (Ha : StackCellBound (i - 1) (j + 1)
      (Znth (StackCellIndex n_pre (i - 1) (j + 1)) table 0)).
  { destruct (Z_lt_ge_dec j n_pre) as [Hjlt | Hjend].
    - exact (proj1 (Hcells (i - 1) (j + 1) ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; lia))).
    - assert (Hjeq : j = n_pre) by lia.
      pose proof (proj1 (Hcells i 0 ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; lia))) as Ha0.
      assert (Hidxeq : StackCellIndex n_pre i 0 =
                       StackCellIndex n_pre (i - 1) (j + 1)) by
        (unfold StackCellIndex; lia).
      rewrite Hidxeq in Ha0.
      exact (StackCellBound_normalize_row_end__cell_dp i j _
        ltac:(lia) ltac:(lia) Ha0). }
  pose proof (Hcells i (j - 1) ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; lia)) as [Hb _].
  pose proof (StackCellBound_add_step__cell_dp i j
    (Znth (StackCellIndex n_pre (i - 1) (j + 1)) table 0)
    (Znth (StackCellIndex n_pre i (j - 1)) table 0)
    ltac:(lia) ltac:(lia) Ha Hb) as Hsum.
  pose proof (StackCellBound_int_range__cell_dp i j _
    ltac:(lia) ltac:(lia) Hsum) as [_ Hmax].
  dump_pre_spatial.
  unfold StackCellIndex in *.
  replace ((i - 1) * (n_pre + 1) + (j + 1) - 0)
    with ((i - 1) * (n_pre + 1) + (j + 1)) by lia.
  replace (i * (n_pre + 1) + (j - 1) - 0)
    with (i * (n_pre + 1) + (j - 1)) by lia.
  exact Hmax.
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_2 : solve_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval. subst retval_2.
  unfold StackRowProgress in PreH22.
  destruct PreH22 as [_ [_ Hprefix]].
  unfold StackTablePrefix in Hprefix.
  destruct Hprefix as [_ [_ Hcells]].
  assert (Ha : StackCellBound (i - 1) (j + 1)
      (Znth (StackCellIndex n_pre (i - 1) (j + 1)) table 0)).
  { destruct (Z_lt_ge_dec j n_pre) as [Hjlt | Hjend].
    - exact (proj1 (Hcells (i - 1) (j + 1) ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; lia))).
    - assert (Hjeq : j = n_pre) by lia.
      pose proof (proj1 (Hcells i 0 ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; lia))) as Ha0.
      assert (Hidxeq : StackCellIndex n_pre i 0 =
                       StackCellIndex n_pre (i - 1) (j + 1)) by
        (unfold StackCellIndex; lia).
      rewrite Hidxeq in Ha0.
      exact (StackCellBound_normalize_row_end__cell_dp i j _
        ltac:(lia) ltac:(lia) Ha0). }
  pose proof (proj1 (Hcells i (j - 1) ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; lia))) as Hb.
  unfold StackCellBound in Ha, Hb.
  destruct Ha as [_ [_ [Ha0 _]]].
  destruct Hb as [_ [_ [Hb0 _]]].
  dump_pre_spatial.
  unfold StackCellIndex in *.
  repeat match goal with
  | |- context [?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil Z).
  replace (0 * (n_pre + 1)) with 0 by ring.
  sep_apply_l_atomic
    (IntArray.undef_full_to_undef_seg f_pre ((n_pre + 1) * (n_pre + 1))).
  rewrite (IntArray.seg_empty f_pre 0 0).
  split_pure_spatial.
  - cancel (IntArray.undef_seg f_pre 0 ((n_pre + 1) * (n_pre + 1))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold StackRowsDone, StackTablePrefix.
      rewrite Zlength_nil.
      repeat split; try lia.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists table_2.
  replace (i * (n_pre + 1) + 0) with (i * (n_pre + 1)) by lia.
  split_pure_spatial.
  - cancel (IntArray.seg f_pre 0 (i * (n_pre + 1)) table_2).
    cancel (IntArray.undef_seg f_pre (i * (n_pre + 1))
      ((n_pre + 1) * (n_pre + 1))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold StackRowsDone in PreH6.
      unfold StackRowProgress.
      destruct PreH6 as [Hi Hprefix].
      split; [exact Hi |].
      split; [lia |].
      replace (i * (n_pre + 1) + 0) with (i * (n_pre + 1)) by lia.
      exact Hprefix.
Qed.

Lemma proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solve_entail_wit_3_split_goal_2 : solve_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_1 : solve_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  pose proof (StackRowProgress_zero_row_extend__cell_dp
    n_pre table_2 j ltac:(lia) ltac:(lia) PreH12) as [Hprogress _].
  exact Hprogress.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_2 : solve_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  pose proof (StackRowProgress_zero_row_extend__cell_dp
    n_pre table_2 j ltac:(lia) ltac:(lia) PreH12)
    as [_ [Hcorrect _]].
  cbn [StackCellIndex] in Hcorrect.
  exact Hcorrect.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_3 : solve_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  pose proof (StackRowProgress_zero_row_extend__cell_dp
    n_pre table_2 j ltac:(lia) ltac:(lia) PreH12)
    as [_ [_ Hbound]].
  cbn [StackCellIndex] in Hbound.
  exact Hbound.
Qed.

Lemma proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_1 : solve_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  pose proof (StackRowProgress_copy_boundary_extend__cell_dp
    n_pre table_2 i ltac:(lia) ltac:(lia) PreH16) as [Hprogress _].
  cbn [StackCellIndex] in Hprogress.
  replace ((((i - 1) * (n_pre + 1) + (0 + 1)) - 0))
    with ((i - 1) * (n_pre + 1) + 1) by lia.
  exact Hprogress.
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_2 : solve_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  pose proof (StackRowProgress_copy_boundary_extend__cell_dp
    n_pre table_2 i ltac:(lia) ltac:(lia) PreH16)
    as [_ [Hcorrect _]].
  cbn [StackCellIndex] in Hcorrect.
  replace ((((i - 1) * (n_pre + 1) + (0 + 1)) - 0))
    with ((i - 1) * (n_pre + 1) + 1) by lia.
  exact Hcorrect.
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_3 : solve_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  pose proof (StackRowProgress_copy_boundary_extend__cell_dp
    n_pre table_2 i ltac:(lia) ltac:(lia) PreH16)
    as [_ [_ Hbound]].
  cbn [StackCellIndex] in Hbound.
  replace ((((i - 1) * (n_pre + 1) + (0 + 1)) - 0))
    with ((i - 1) * (n_pre + 1) + 1) by lia.
  exact Hbound.
Qed.

Lemma proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_5_3_split_goal_1 : solve_entail_wit_5_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (StackRowProgress_add_step_extend__cell_dp
    n_pre table_2 i j ltac:(lia) ltac:(lia) ltac:(lia) PreH22)
    as [Hprogress _].
  cbn [StackCellIndex] in Hprogress.
  repeat match goal with
  | |- context [?x - 0] => replace (x - 0) with x by lia
  end.
  exact Hprogress.
Qed.

Lemma proof_of_solve_entail_wit_5_3_split_goal_2 : solve_entail_wit_5_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (StackRowProgress_add_step_extend__cell_dp
    n_pre table_2 i j ltac:(lia) ltac:(lia) ltac:(lia) PreH22)
    as [_ [Hcorrect _]].
  cbn [StackCellIndex] in Hcorrect.
  repeat match goal with
  | |- context [?x - 0] => replace (x - 0) with x by lia
  end.
  exact Hcorrect.
Qed.

Lemma proof_of_solve_entail_wit_5_3_split_goal_3 : solve_entail_wit_5_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (StackRowProgress_add_step_extend__cell_dp
    n_pre table_2 i j ltac:(lia) ltac:(lia) ltac:(lia) PreH22)
    as [_ [_ Hbound]].
  cbn [StackCellIndex] in Hbound.
  repeat match goal with
  | |- context [?x - 0] => replace (x - 0) with x by lia
  end.
  exact Hbound.
Qed.

Lemma proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_5_3_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists table_2.
  replace (i * (n_pre + 1) + j + 1)
    with (i * (n_pre + 1) + (j + 1)) by lia.
  split_pure_spatial.
  - cancel (IntArray.seg f_pre 0 (i * (n_pre + 1) + (j + 1)) table_2).
    cancel (IntArray.undef_seg f_pre (i * (n_pre + 1) + (j + 1))
      ((n_pre + 1) * (n_pre + 1))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = n_pre + 1) by lia.
  subst j.
  Exists table_2.
  replace (i * (n_pre + 1) + (n_pre + 1))
    with ((i + 1) * (n_pre + 1)) by ring.
  split_pure_spatial.
  - cancel (IntArray.seg f_pre 0 ((i + 1) * (n_pre + 1)) table_2).
    cancel (IntArray.undef_seg f_pre ((i + 1) * (n_pre + 1))
      ((n_pre + 1) * (n_pre + 1))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold StackRowProgress in PreH8.
      unfold StackRowsDone.
      destruct PreH8 as [Hi [_ Hprefix]].
      split; [lia |].
      replace ((i + 1) * (n_pre + 1))
        with (i * (n_pre + 1) + (n_pre + 1)) by ring.
      exact Hprefix.
Qed.

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with (n_pre + 1) in * by lia.
  Exists table_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full f_pre 0
      ((n_pre + 1) * (n_pre + 1)) table_2).
    replace (f_pre + 0 * sizeof (INT)) with f_pre by lia.
    replace ((n_pre + 1) * (n_pre + 1) - 0)
      with ((n_pre + 1) * (n_pre + 1)) by lia.
    cancel (IntArray.full f_pre
      ((n_pre + 1) * (n_pre + 1)) table_2).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial.
      unfold StackRowsDone in PreH6.
      destruct PreH6 as [_ Hprefix].
      unfold StackTablePrefix in Hprefix.
      destruct Hprefix as [_ [_ Hcells]].
      specialize (Hcells n_pre 0 ltac:(lia) ltac:(lia) ltac:(
        unfold StackCellIndex; nia)).
      destruct Hcells as [_ Hcorrect].
      unfold StackCellCorrect in Hcorrect.
      unfold StackCellIndex in Hcorrect.
      replace (n_pre * (n_pre + 1) + 0) with (n_pre * (n_pre + 1))
        in Hcorrect by lia.
      apply StackCompletionCount_zero_to_StackSequenceCount.
      apply Hcorrect.
      lia.
Qed.

Lemma proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((n_pre * (n_pre + 1)) + 0)
    with (n_pre * (n_pre + 1)) by lia.
  exact PreH9.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_return_wit_1_split_goal_1.
Qed.
