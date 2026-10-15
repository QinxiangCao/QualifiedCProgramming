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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P039_435B_pasha_maximizes_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P039_435B_pasha_maximizes_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists digits.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; intros; apply PreH7; lia).
    all: try (dump_pre_spatial;
      apply greedy_progress_initial__initialization; lia).
    all: try (dump_pre_spatial; apply GreedySelectionReady_universal).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cur_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity; try assumption.
    apply first_maximum_prefix_singleton__selection_scan.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cur_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity; try assumption.
    eapply first_maximum_prefix_extend_strict_app_zero__selection_scan;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cur_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity; try assumption.
    eapply first_maximum_prefix_extend_nonstrict_app_zero__selection_scan;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = n_pre) by lia.
  subst j.
  assert (Hreachable : ReachableFirstMaximum cur_2 i k best).
  {
    unfold ReachableFirstMaximum.
    rewrite PreH8.
    rewrite Z.min_l by lia.
    exact PreH19.
  }
  assert (Hclosure : GreedyExchangeClosure cur_2 i k best).
  {
    eapply GreedySelectionReady_specialize; eauto.
  }
  pose proof (move_left_same__selection_exchange cur_2 best ltac:(lia))
    as Hsame.
  Exists cur_2 cur_2 k.
  rewrite Hsame.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = i + k + 1) by lia.
  subst j.
  assert (Hreachable : ReachableFirstMaximum cur_2 i k best).
  {
    unfold ReachableFirstMaximum.
    rewrite PreH9.
    rewrite Z.min_r by lia.
    exact PreH20.
  }
  assert (Hclosure : GreedyExchangeClosure cur_2 i k best).
  {
    eapply GreedySelectionReady_specialize; eauto.
  }
  pose proof (move_left_same__selection_exchange cur_2 best ltac:(lia))
    as Hsame.
  Exists cur_2 cur_2 k.
  rewrite Hsame.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst cur_2.
  assert (Hstep :
    replace_Znth (j - 1)
      (Znth j (move_left before_2 best j ++ (@cons Z 0 (@nil Z))) 0)
      (replace_Znth j
        (Znth (j - 1)
          (move_left before_2 best j ++ (@cons Z 0 (@nil Z))) 0)
        (move_left before_2 best j ++ (@cons Z 0 (@nil Z)))) =
    move_left before_2 best (j - 1) ++ (@cons Z 0 (@nil Z))).
  { apply move_left_step_padded__bubble_transition. lia. }
  Exists (move_left before_2 best (j - 1)) before_2 start_k_2.
  rewrite Hstep.
  split_pure_spatial.
  - cancel (CharArray.full d_pre (n_pre + 1)
      (move_left before_2 best (j - 1) ++ (@cons Z 0 (@nil Z)))).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + rewrite move_left_Zlength__bubble_transition by lia.
      exact PreH8.
    + intros p Hp.
      eapply move_left_preserves_range__bubble_transition.
      * lia.
      * intros q Hq. apply PreH12. lia.
      * lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hji : j = i) by lia.
  subst j.
  subst cur_2.
  pose proof PreH24 as Hprogress_fields.
  unfold GreedyProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [_ [_ [_ [Hreach_before _]]]].
  assert (Hreach_after :
    SwapReach digits (move_left before best i)
      (k_pre - (start_k - (best - i)))).
  {
    replace (k_pre - (start_k - (best - i))) with
      ((k_pre - start_k) + (best - i)) by lia.
    eapply swap_reach_move_left_after__bubble_transition.
    - lia.
    - exact Hreach_before.
  }
  assert (Hprogress_after :
    GreedyProgress digits k_pre (move_left before best i) (i + 1) k).
  {
    rewrite PreH20.
    eapply GreedyExchangeClosure_preserves_progress.
    - exact PreH23.
    - exact PreH24.
    - exact PreH26.
    - apply move_left_Zlength__bubble_transition. lia.
    - exact Hreach_after.
  }
  Exists (move_left before best i).
  split_pure_spatial.
  - cancel (CharArray.full d_pre (n_pre + 1)
      (move_left before best i ++ (@cons Z 0 (@nil Z)))).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    apply GreedySelectionReady_universal.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cur.
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial.
    apply greedy_progress_terminal_spec__final_result with (pos := i) (remaining := k).
    + exact PreH14.
    + left. lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cur.
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial.
    apply greedy_progress_terminal_spec__final_result with (pos := i) (remaining := k).
    + exact PreH15.
    + right. lia.
Qed.
