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
From SimpleC.EE.LLM_bench.Algorithms.rod_cutting Require Import rod_cutting_goal.
From SimpleC.EE.LLM_bench.Algorithms.rod_cutting Require Import rod_cutting_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib.
Local Open Scope sac.

Lemma proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full price_pre (n_pre + 1) price_l).
    cancel (IntArray.undef_seg revenue_pre 1 (n_pre + 1)).
    sep_apply_l_atomic (IntArray.seg_single revenue_pre 0 0).
    change (0 + 1) with 1.
    cancel (IntArray.seg revenue_pre 0 1 (0 :: nil)).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      unfold RodCutRevenueTable.
      intros rod_len Hrod_len.
      assert (rod_len = 0) by lia.
      subst rod_len.
      simpl.
      apply rod_cut_optimal_revenue_zero__boundary_states.
    + dump_pre_spatial.
      intros k Hk.
      assert (k = 0) by lia.
      subst k.
      rewrite Znth0_cons.
      split; lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_2_split_goal_1 : rod_cutting_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  apply PreH11; assumption.
Qed.

Lemma proof_of_rod_cutting_entail_wit_2_split_goal_2 : rod_cutting_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  unfold RodCutScanBest.
  apply MaxMin.max_default_default.
  intros piece Hpiece.
  lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_2_split_goal_3 : rod_cutting_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  apply PreH6; assumption.
Qed.

Lemma proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rod_cutting_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_rod_cutting_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_rod_cutting_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_rod_cutting_entail_wit_4_1_split_goal_1 : rod_cutting_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  replace ((j - i) - 0) with (j - i) in PreH1 by lia.
  unfold RodCutScanBest in *.
  replace ((j - i) - 0) with (j - i) by lia.
  eapply rod_cut_scan_best_step__scan_transitions; [lia | exact PreH22 |].
  left; split; [lia | reflexivity].
Qed.

Lemma proof_of_rod_cutting_entail_wit_4_1 : rod_cutting_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rod_cutting_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_rod_cutting_entail_wit_4_2_split_goal_1 : rod_cutting_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  replace ((j - i) - 0) with (j - i) in PreH1 by lia.
  unfold RodCutScanBest in *.
  replace ((j - i) - 0) with (j - i) by lia.
  eapply rod_cut_scan_best_step__scan_transitions; [lia | exact PreH22 |].
  right; split; [lia | reflexivity].
Qed.

Lemma proof_of_rod_cutting_entail_wit_4_2 : rod_cutting_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rod_cutting_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_rod_cutting_entail_wit_5_split_goal_1 : rod_cutting_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z_lt_ge_dec k_2 j) as [Hlt | Hge].
  - rewrite app_Znth1 by lia.
    apply PreH16. lia.
  - assert (k_2 = j) by lia.
    subst k_2.
    rewrite app_Znth2 by lia.
    rewrite PreH13.
    replace (j - j) with 0 by lia.
    rewrite Znth0_cons.
    lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_5_split_goal_2 : rod_cutting_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = j + 1) by lia.
  subst i.
  eapply (rod_cut_revenue_table_snoc__table_extension
    price_l revenue_l_2 j best).
  - exact PreH7.
  - exact PreH13.
  - pose proof (PreH6 j ltac:(lia)) as Hjprice.
    exact (proj1 Hjprice).
  - exact PreH14.
  - exact PreH15.
Qed.

Lemma proof_of_rod_cutting_entail_wit_5_split_goal_3 : rod_cutting_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH13.
  lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_5_split_goal_4 : rod_cutting_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6.
  assumption.
Qed.

Lemma proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rod_cutting_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_rod_cutting_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_rod_cutting_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_rod_cutting_entail_wit_5_split_goal_4.
Qed.

Lemma proof_of_rod_cutting_return_wit_1 : rod_cutting_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = n_pre + 1) by lia.
  rewrite H in PreH9, PreH10, PreH11.
  rewrite H.
  Exists revenue_l_2.
  split_pure_spatial.
  - cancel (IntArray.full price_pre (n_pre + 1) price_l).
    sep_apply_l_atomic
      (IntArray.seg_to_full revenue_pre 0 (n_pre + 1) revenue_l_2).
    replace (revenue_pre + 0 * sizeof(INT)) with revenue_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel (IntArray.full revenue_pre (n_pre + 1) revenue_l_2).
  - split_pures.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial.
      replace (n_pre - 0) with n_pre by lia.
      reflexivity.
    + dump_pre_spatial. assumption.
Qed.
