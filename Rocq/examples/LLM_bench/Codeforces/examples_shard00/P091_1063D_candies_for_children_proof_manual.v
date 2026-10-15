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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P091_1063D_candies_for_children_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P091_1063D_candies_for_children_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P091_1063D_candies_for_children_lib.
Local Open Scope sac.

Lemma proof_of_maxll_return_wit_1_split_goal_1 : maxll_return_wit_1_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
unfold MaxResult. rewrite Z.max_l by lia. reflexivity. Qed.

Lemma proof_of_maxll_return_wit_1 : maxll_return_wit_1.
Proof. aggressive_pre_process. Goal_apply proof_of_maxll_return_wit_1_split_goal_1. Qed.

Lemma proof_of_maxll_return_wit_2_split_goal_1 : maxll_return_wit_2_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
unfold MaxResult. rewrite Z.max_r by lia. reflexivity. Qed.

Lemma proof_of_maxll_return_wit_2 : maxll_return_wit_2.
Proof. aggressive_pre_process. Goal_apply proof_of_maxll_return_wit_2_split_goal_1. Qed.

Lemma proof_of_minll_return_wit_1_split_goal_1 : minll_return_wit_1_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
unfold MinResult. rewrite Z.min_l by lia. reflexivity. Qed.

Lemma proof_of_minll_return_wit_1 : minll_return_wit_1.
Proof. aggressive_pre_process. Goal_apply proof_of_minll_return_wit_1_split_goal_1. Qed.

Lemma proof_of_minll_return_wit_2_split_goal_1 : minll_return_wit_2_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
unfold MinResult. rewrite Z.min_r by lia. reflexivity. Qed.

Lemma proof_of_minll_return_wit_2 : minll_return_wit_2.
Proof. aggressive_pre_process. Goal_apply proof_of_minll_return_wit_2_split_goal_1. Qed.

Lemma proof_of_ceildiv_return_wit_1_split_goal_1 : ceildiv_return_wit_1_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
rewrite Z.quot_div_nonneg by lia.
pose proof (Z.div_mod (a_pre + b_pre - 1) b_pre ltac:(lia)).
pose proof (Z.mod_pos_bound (a_pre + b_pre - 1) b_pre ltac:(lia)). nia. Qed.

Lemma proof_of_ceildiv_return_wit_1_split_goal_2 : ceildiv_return_wit_1_split_goal_2.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
rewrite Z.quot_div_nonneg by lia.
pose proof (Z.div_mod (a_pre + b_pre - 1) b_pre ltac:(lia)).
pose proof (Z.mod_pos_bound (a_pre + b_pre - 1) b_pre ltac:(lia)). nia. Qed.

Lemma proof_of_ceildiv_return_wit_1 : ceildiv_return_wit_1.
Proof. aggressive_pre_process.
- Goal_apply proof_of_ceildiv_return_wit_1_split_goal_1.
- Goal_apply proof_of_ceildiv_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_ceildiv_return_wit_2_split_goal_1 : ceildiv_return_wit_2_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
replace a_pre with (- (- a_pre)) at 2 by lia.
rewrite Z.quot_opp_l by lia.
rewrite Z.quot_div_nonneg by lia.
pose proof (Z.div_mod (- a_pre) b_pre ltac:(lia)).
pose proof (Z.mod_pos_bound (- a_pre) b_pre ltac:(lia)). nia. Qed.

Lemma proof_of_ceildiv_return_wit_2_split_goal_2 : ceildiv_return_wit_2_split_goal_2.
Proof. LLM_pre_process ltac:(lia || nia || int_auto).
replace a_pre with (- (- a_pre)) at 1 by lia.
rewrite Z.quot_opp_l by lia.
rewrite Z.quot_div_nonneg by lia.
pose proof (Z.div_mod (- a_pre) b_pre ltac:(lia)).
pose proof (Z.mod_pos_bound (- a_pre) b_pre ltac:(lia)). nia. Qed.

Lemma proof_of_ceildiv_return_wit_2 : ceildiv_return_wit_2.
Proof. aggressive_pre_process.
- Goal_apply proof_of_ceildiv_return_wit_2_split_goal_1.
- Goal_apply proof_of_ceildiv_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_check_entail_wit_1_1_split_goal_1 : check_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hadd : add_pre = 1) by lia.
  subst add_pre.
  assert (Hqpos : 0 < q_pre) by lia.
  unfold MinResult in PreH1, PreH8.
  unfold MaxResult in PreH2, PreH5.
  subst retval_2; subst retval_3; subst retval; subst retval_5.
  unfold CandyFeasibleInterval.
  intros num Hnum.
  unfold QuotientBlock in PreH21.
  specialize (PreH21 num Hnum).
  assert (Hnumpos : 0 < num) by lia.
  pose proof (Z.mul_div_le (k_pre - 1) num Hnumpos) as Hkdiv.
  rewrite <- PreH21 in Hkdiv.
  assert (Hnumq : num <= num * q_pre).
  { replace num with (num * 1) at 1 by ring.
    apply Z.mul_le_mono_nonneg_l; lia. }
  assert (Hkx : 0 <= k_pre - x_pre) by lia.
  assert (Hupper_nonneg : 0 <= k_pre - x_pre + 1 + 2 * n_pre - x_pre) by lia.
  unfold CandyArithmeticCandidate.
  rewrite <- PreH21.
  split.
  - intros [Hrange [_ [Hh [Hcap Hlast]]]].
    split.
    + apply Z.max_lub.
      * apply Z.max_lub.
        -- lia.
        -- apply (proj2 (z_ceil_characterization__check_feasible_intervals
                            (k_pre - x_pre + 1 - x_pre) q_pre retval_4 num
                            Hqpos PreH6 PreH7)).
           lia.
      * apply (proj2 (z_ceil_characterization__check_feasible_intervals
                         (k_pre - x_pre + 1 + n_pre) (q_pre + 1)
                         retval_6 num ltac:(lia) PreH3 PreH4)).
        lia.
    + apply Z.min_glb.
      * apply Z.min_glb.
        -- lia.
        -- apply (proj2 (z_le_div_iff_mul_le__check_feasible_intervals
                            (k_pre - x_pre + 1 - 1) q_pre num
                            ltac:(lia) Hqpos)); lia.
      * apply (proj2 (z_le_div_iff_mul_le__check_feasible_intervals
                         (k_pre - x_pre + 1 + 2 * n_pre - x_pre)
                         (q_pre + 1) num Hupper_nonneg ltac:(lia))); lia.
  - intros [Hlo Hhi].
    assert (Hlo4 : retval_4 <= num).
    { eapply Z.le_trans; [apply Z.le_max_r |].
      eapply Z.le_trans; [apply Z.le_max_l | exact Hlo]. }
    assert (Hlo6 : retval_6 <= num).
    { eapply Z.le_trans; [apply Z.le_max_r | exact Hlo]. }
    assert (Hhi1 : num <= (k_pre - x_pre + 1 - 1) ÷ q_pre).
    { eapply Z.le_trans; [exact Hhi |].
      eapply Z.le_trans; [apply Z.le_min_l | apply Z.le_min_r]. }
    assert (Hhi2 : num <=
      (k_pre - x_pre + 1 + 2 * n_pre - x_pre) ÷ (q_pre + 1)).
    { eapply Z.le_trans; [exact Hhi | apply Z.le_min_r]. }
    pose proof (proj1 (z_ceil_characterization__check_feasible_intervals
                         (k_pre - x_pre + 1 - x_pre) q_pre retval_4 num
                         Hqpos PreH6 PreH7) Hlo4) as Hceil1.
    pose proof (proj1 (z_ceil_characterization__check_feasible_intervals
                         (k_pre - x_pre + 1 + n_pre) (q_pre + 1)
                         retval_6 num ltac:(lia) PreH3 PreH4) Hlo6) as Hceil2.
    pose proof (proj1 (z_le_div_iff_mul_le__check_feasible_intervals
                         (k_pre - x_pre + 1 - 1) q_pre num ltac:(lia) Hqpos)
                      Hhi1) as Hmul1.
    pose proof (proj1 (z_le_div_iff_mul_le__check_feasible_intervals
                         (k_pre - x_pre + 1 + 2 * n_pre - x_pre)
                         (q_pre + 1) num Hupper_nonneg ltac:(lia))
                      Hhi2) as Hmul2.
    split; [lia |].
    split; [right; reflexivity |].
    repeat split; lia.
Qed.

Lemma proof_of_check_entail_wit_1_1_split_goal_2 : check_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MinResult in PreH1, PreH8.
  subst retval_2; subst retval_3.
  eapply Z.le_trans; [apply Z.le_min_l | apply Z.le_min_l].
Qed.

Lemma proof_of_check_entail_wit_1_1_split_goal_3 : check_entail_wit_1_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MaxResult in PreH2, PreH5.
  subst retval; subst retval_5.
  eapply Z.le_trans; [apply Z.le_max_l | apply Z.le_max_l].
Qed.

Lemma proof_of_check_entail_wit_1_1 : check_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_entail_wit_1_1_split_goal_1.
  - Goal_apply proof_of_check_entail_wit_1_1_split_goal_2.
  - Goal_apply proof_of_check_entail_wit_1_1_split_goal_3.
Qed.

Lemma proof_of_check_entail_wit_1_2_split_goal_1 : check_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst add_pre.
  assert (Hqpos : 0 < q_pre) by lia.
  unfold MinResult in PreH1, PreH8.
  unfold MaxResult in PreH2, PreH5.
  subst retval_2; subst retval_3; subst retval; subst retval_5.
  unfold CandyFeasibleInterval.
  intros num Hnum.
  unfold QuotientBlock in PreH21.
  specialize (PreH21 num Hnum).
  assert (Hnumpos : 0 < num) by lia.
  pose proof (Z.mul_div_le (k_pre - 1) num Hnumpos) as Hkdiv.
  rewrite <- PreH21 in Hkdiv.
  assert (Hnumq : num <= num * q_pre).
  { replace num with (num * 1) at 1 by ring.
    apply Z.mul_le_mono_nonneg_l; lia. }
  assert (Hkx : 0 <= k_pre - x_pre) by lia.
  assert (Hupper_nonneg : 0 <= k_pre - x_pre + 0 + 2 * n_pre - x_pre) by lia.
  unfold CandyArithmeticCandidate.
  rewrite <- PreH21.
  split.
  - intros [Hrange [_ [Hh [Hcap Hlast]]]].
    split.
    + apply Z.max_lub.
      * apply Z.max_lub.
        -- lia.
        -- apply (proj2 (z_ceil_characterization__check_feasible_intervals
                            (k_pre - x_pre + 0 - x_pre) q_pre retval_4 num
                            Hqpos PreH6 PreH7)).
           lia.
      * apply (proj2 (z_ceil_characterization__check_feasible_intervals
                         (k_pre - x_pre + 0 + n_pre) (q_pre + 1)
                         retval_6 num ltac:(lia) PreH3 PreH4)).
        lia.
    + apply Z.min_glb.
      * apply Z.min_glb.
        -- lia.
        -- apply (proj2 (z_le_div_iff_mul_le__check_feasible_intervals
                            (k_pre - x_pre + 0) q_pre num
                            ltac:(lia) Hqpos)); lia.
      * apply (proj2 (z_le_div_iff_mul_le__check_feasible_intervals
                         (k_pre - x_pre + 0 + 2 * n_pre - x_pre)
                         (q_pre + 1) num Hupper_nonneg ltac:(lia))); lia.
  - intros [Hlo Hhi].
    assert (Hlo4 : retval_4 <= num).
    { eapply Z.le_trans; [apply Z.le_max_r |].
      eapply Z.le_trans; [apply Z.le_max_l | exact Hlo]. }
    assert (Hlo6 : retval_6 <= num).
    { eapply Z.le_trans; [apply Z.le_max_r | exact Hlo]. }
    assert (Hhi1 : num <= (k_pre - x_pre + 0) ÷ q_pre).
    { eapply Z.le_trans; [exact Hhi |].
      eapply Z.le_trans; [apply Z.le_min_l | apply Z.le_min_r]. }
    assert (Hhi2 : num <=
      (k_pre - x_pre + 0 + 2 * n_pre - x_pre) ÷ (q_pre + 1)).
    { eapply Z.le_trans; [exact Hhi | apply Z.le_min_r]. }
    pose proof (proj1 (z_ceil_characterization__check_feasible_intervals
                         (k_pre - x_pre + 0 - x_pre) q_pre retval_4 num
                         Hqpos PreH6 PreH7) Hlo4) as Hceil1.
    pose proof (proj1 (z_ceil_characterization__check_feasible_intervals
                         (k_pre - x_pre + 0 + n_pre) (q_pre + 1)
                         retval_6 num ltac:(lia) PreH3 PreH4) Hlo6) as Hceil2.
    pose proof (proj1 (z_le_div_iff_mul_le__check_feasible_intervals
                         (k_pre - x_pre + 0) q_pre num ltac:(lia) Hqpos)
                      Hhi1) as Hmul1.
    pose proof (proj1 (z_le_div_iff_mul_le__check_feasible_intervals
                         (k_pre - x_pre + 0 + 2 * n_pre - x_pre)
                         (q_pre + 1) num Hupper_nonneg ltac:(lia))
                      Hhi2) as Hmul2.
    split; [lia |].
    split; [left; reflexivity |].
    repeat split; lia.
Qed.

Lemma proof_of_check_entail_wit_1_2_split_goal_2 : check_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MinResult in PreH1, PreH8.
  subst retval_2; subst retval_3.
  eapply Z.le_trans; [apply Z.le_min_l | apply Z.le_min_l].
Qed.

Lemma proof_of_check_entail_wit_1_2_split_goal_3 : check_entail_wit_1_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MaxResult in PreH2, PreH5.
  subst retval; subst retval_5.
  eapply Z.le_trans; [apply Z.le_max_l | apply Z.le_max_l].
Qed.

Lemma proof_of_check_entail_wit_1_2 : check_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_entail_wit_1_2_split_goal_1.
  - Goal_apply proof_of_check_entail_wit_1_2_split_goal_2.
  - Goal_apply proof_of_check_entail_wit_1_2_split_goal_3.
Qed.

Lemma proof_of_check_entail_wit_1_3_split_goal_1 : check_entail_wit_1_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst add_pre; subst q_pre.
  unfold MinResult in PreH1.
  unfold MaxResult in PreH2.
  subst retval_2; subst retval.
  rewrite Z.quot_1_r in *.
  assert (retval_3 = k_pre - x_pre + n_pre) by nia.
  subst retval_3.
  unfold CandyFeasibleInterval.
  intros num Hnum.
  unfold QuotientBlock in PreH20.
  specialize (PreH20 num Hnum).
  unfold CandyArithmeticCandidate.
  rewrite <- PreH20.
  split.
  - intros [Hrange [_ [Hh [Hcap Hlast]]]].
    split.
    + apply Z.max_lub; nia.
    + apply Z.min_glb.
      * lia.
      * nia.
  - intros [Hlo Hhi].
    pose proof (Z.le_max_r L_pre (k_pre - x_pre + n_pre)).
    pose proof (Z.le_min_r R_pre (k_pre - x_pre + 2 * n_pre - x_pre)).
    split; [lia |].
    split; [left; reflexivity |].
    repeat split; nia.
Qed.

Lemma proof_of_check_entail_wit_1_3_split_goal_2 : check_entail_wit_1_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MinResult in PreH1.
  subst retval_2.
  apply Z.le_min_l.
Qed.

Lemma proof_of_check_entail_wit_1_3_split_goal_3 : check_entail_wit_1_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MaxResult in PreH2.
  subst retval.
  apply Z.le_max_l.
Qed.

Lemma proof_of_check_entail_wit_1_3 : check_entail_wit_1_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_entail_wit_1_3_split_goal_1.
  - Goal_apply proof_of_check_entail_wit_1_3_split_goal_2.
  - Goal_apply proof_of_check_entail_wit_1_3_split_goal_3.
Qed.

Lemma proof_of_check_entail_wit_1_4_split_goal_1 : check_entail_wit_1_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (add_pre = 1) by lia.
  subst add_pre; subst q_pre.
  unfold MinResult in PreH1.
  unfold MaxResult in PreH2.
  subst retval_2; subst retval.
  rewrite Z.quot_1_r in *.
  assert (retval_3 = k_pre - x_pre + 1 + n_pre) by nia.
  subst retval_3.
  unfold CandyFeasibleInterval.
  intros num Hnum.
  unfold QuotientBlock in PreH20.
  specialize (PreH20 num Hnum).
  unfold CandyArithmeticCandidate.
  rewrite <- PreH20.
  split.
  - intros [Hrange [_ [Hh [Hcap Hlast]]]].
    split.
    + apply Z.max_lub; nia.
    + apply Z.min_glb.
      * lia.
      * nia.
  - intros [Hlo Hhi].
    pose proof (Z.le_max_r L_pre (k_pre - x_pre + 1 + n_pre)).
    pose proof (Z.le_min_r R_pre (k_pre - x_pre + 1 + 2 * n_pre - x_pre)).
    split; [lia |].
    split; [right; reflexivity |].
    repeat split; nia.
Qed.

Lemma proof_of_check_entail_wit_1_4_split_goal_2 : check_entail_wit_1_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MinResult in PreH1.
  subst retval_2.
  apply Z.le_min_l.
Qed.

Lemma proof_of_check_entail_wit_1_4_split_goal_3 : check_entail_wit_1_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MaxResult in PreH2.
  subst retval.
  apply Z.le_max_l.
Qed.

Lemma proof_of_check_entail_wit_1_4 : check_entail_wit_1_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_entail_wit_1_4_split_goal_1.
  - Goal_apply proof_of_check_entail_wit_1_4_split_goal_2.
  - Goal_apply proof_of_check_entail_wit_1_4_split_goal_3.
Qed.

Lemma proof_of_check_return_wit_1_split_goal_1 : check_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  eapply candy_search_block_skip_infeasible__check_qzero_returns; eauto; left; lia.
Qed.

Lemma proof_of_check_return_wit_1 : check_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_2_split_goal_1 : check_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  eapply candy_search_block_skip_infeasible__check_qzero_returns; eauto; left; lia.
Qed.

Lemma proof_of_check_return_wit_2 : check_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_3_split_goal_1 : check_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  eapply candy_search_block_skip_infeasible__check_qzero_returns; eauto; right; lia.
Qed.

Lemma proof_of_check_return_wit_3 : check_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_4_split_goal_1 : check_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  eapply candy_search_block_skip_infeasible__check_qzero_returns; eauto; right; lia.
Qed.

Lemma proof_of_check_return_wit_4 : check_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_5_split_goal_1 : check_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply candy_search_block_phase_update__check_block_updates; eauto; lia.
Qed.

Lemma proof_of_check_return_wit_5 : check_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_6_split_goal_1 : check_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply candy_phase_preserve__check_block_updates; eauto.
  intros num Hr Hc.
  match goal with H : CandyFeasibleInterval _ _ _ _ _ _ _ _ _ |- _ =>
    apply (proj1 (H num Hr)) in Hc end.
  lia.
Qed.

Lemma proof_of_check_return_wit_6 : check_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_7_split_goal_1 : check_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply candy_phase_preserve__check_block_updates; eauto.
  intros num Hr Hc.
  match goal with H : CandyFeasibleInterval _ _ _ _ _ _ _ _ _ |- _ =>
    apply (proj1 (H num Hr)) in Hc end.
  lia.
Qed.

Lemma proof_of_check_return_wit_7 : check_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_check_partial_solve_wit_1_pure_split_goal_1 : check_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply Z.quot_le_lower_bound; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_1_pure_split_goal_2 : check_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply Z.quot_le_upper_bound; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_1_pure : check_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_check_partial_solve_wit_2_pure_split_goal_1 : check_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply Z.quot_le_lower_bound; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_2_pure_split_goal_2 : check_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply Z.quot_le_upper_bound; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_2_pure_split_goal_3 : check_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply Z.quot_le_upper_bound; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_2_pure_split_goal_4 : check_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply Z.quot_le_lower_bound; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_2_pure : check_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_check_partial_solve_wit_2_pure_split_goal_3.
  - Goal_apply proof_of_check_partial_solve_wit_2_pure_split_goal_4.
Qed.

Lemma proof_of_check_partial_solve_wit_8_pure_split_goal_1 : check_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold MaxResult in *. lia.
Qed.

Lemma proof_of_check_partial_solve_wit_8_pure_split_goal_2 : check_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold MaxResult in *. nia.
Qed.

Lemma proof_of_check_partial_solve_wit_8_pure : check_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_check_partial_solve_wit_10_pure_split_goal_1 : check_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold MaxResult in *. lia.
Qed.

Lemma proof_of_check_partial_solve_wit_10_pure_split_goal_2 : check_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold MaxResult in *. nia.
Qed.

Lemma proof_of_check_partial_solve_wit_10_pure : check_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_10_pure_split_goal_2.
Qed.

Lemma proof_of_check_partial_solve_wit_15_pure_split_goal_1 : check_partial_solve_wit_15_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  unfold MinResult in *.
  subst retval.
  match goal with |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[Hle Heq]|[Hle Heq]] end; rewrite Heq;
    try lia.
  all: first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_15_pure_split_goal_2 : check_partial_solve_wit_15_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  unfold MinResult in *.
  subst retval.
  match goal with |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[Hle Heq]|[Hle Heq]] end; rewrite Heq;
    try lia.
  all: first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_15_pure_split_goal_3 : check_partial_solve_wit_15_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_15_pure_split_goal_4 : check_partial_solve_wit_15_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_15_pure : check_partial_solve_wit_15_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_15_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_15_pure_split_goal_2.
  - Goal_apply proof_of_check_partial_solve_wit_15_pure_split_goal_3.
  - Goal_apply proof_of_check_partial_solve_wit_15_pure_split_goal_4.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure_split_goal_1 : check_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  unfold MinResult in *.
  subst retval.
  match goal with |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[Hle Heq]|[Hle Heq]] end; rewrite Heq;
    try lia.
  all: first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure_split_goal_2 : check_partial_solve_wit_16_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  unfold MinResult in *.
  subst retval.
  match goal with |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[Hle Heq]|[Hle Heq]] end; rewrite Heq;
    try lia.
  all: first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure_split_goal_3 : check_partial_solve_wit_16_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure_split_goal_4 : check_partial_solve_wit_16_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure_split_goal_5 : check_partial_solve_wit_16_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure_split_goal_6 : check_partial_solve_wit_16_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_16_pure : check_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_16_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_16_pure_split_goal_2.
  - Goal_apply proof_of_check_partial_solve_wit_16_pure_split_goal_3.
  - Goal_apply proof_of_check_partial_solve_wit_16_pure_split_goal_4.
  - Goal_apply proof_of_check_partial_solve_wit_16_pure_split_goal_5.
  - Goal_apply proof_of_check_partial_solve_wit_16_pure_split_goal_6.
Qed.

Lemma proof_of_check_partial_solve_wit_17_pure_split_goal_1 : check_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_17_pure_split_goal_2 : check_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_17_pure_split_goal_3 : check_partial_solve_wit_17_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_17_pure_split_goal_4 : check_partial_solve_wit_17_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_17_pure : check_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_17_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_17_pure_split_goal_2.
  - Goal_apply proof_of_check_partial_solve_wit_17_pure_split_goal_3.
  - Goal_apply proof_of_check_partial_solve_wit_17_pure_split_goal_4.
Qed.

Lemma proof_of_check_partial_solve_wit_18_pure_split_goal_1 : check_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_18_pure_split_goal_2 : check_partial_solve_wit_18_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_18_pure_split_goal_3 : check_partial_solve_wit_18_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_18_pure_split_goal_4 : check_partial_solve_wit_18_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  first [apply Z.quot_le_lower_bound | apply Z.quot_le_upper_bound]; lia.
Qed.

Lemma proof_of_check_partial_solve_wit_18_pure : check_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_partial_solve_wit_18_pure_split_goal_1.
  - Goal_apply proof_of_check_partial_solve_wit_18_pure_split_goal_2.
  - Goal_apply proof_of_check_partial_solve_wit_18_pure_split_goal_3.
  - Goal_apply proof_of_check_partial_solve_wit_18_pure_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_5_split_goal_1 : solver_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos ((r_pre - l_pre) + n_pre) n_pre ltac:(lia) ltac:(lia)).
  cancel.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_5_split_goal_2 : solver_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos ((r_pre - l_pre) + n_pre) n_pre ltac:(lia) ltac:(lia)).
  cancel.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CandySearchPrefix, MaxMin.max_value_of_subset_with_default.
  right.
  split; [| reflexivity].
  intros [num add] [Hcandidate Hlt].
  unfold CandyArithmeticCandidate in Hcandidate.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos ((r_pre - l_pre) + n_pre) n_pre ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos ((r_pre - l_pre) + n_pre) n_pre ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH4.
  apply candy_prefix_to_phase0_block__solver_quotient_routes.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst z.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  assert (Hqnonneg : 0 <= (k_pre - 1) / cur) by
    (apply Z.div_pos; lia).
  assert (Hqpos : 0 < (k_pre - 1) / cur) by lia.
  assert (Hinner : (k_pre - 1) ÷ cur = (k_pre - 1) / cur) by
    (apply Z.quot_div_nonneg; lia).
  rewrite Hinner in PreH1.
  rewrite Z.quot_div_nonneg in PreH1 by lia.
  rewrite Z.quot_div_nonneg by lia.
  unfold QuotientBlock.
  intros num Hnum.
  pose proof
    (quotient_block_plateau__solver_quotient_routes
       (k_pre - 1) cur ltac:(lia) ltac:(lia) Hqpos) as [_ Hplateau].
  apply Hplateau.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_3 : solver_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_4 : solver_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH4.
  apply candy_prefix_to_phase0_block__solver_quotient_routes.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst z.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  assert (Hqnonneg : 0 <= (k_pre - 1) / cur) by
    (apply Z.div_pos; lia).
  assert (Hqpos : 0 < (k_pre - 1) / cur) by lia.
  assert (Hinner : (k_pre - 1) ÷ cur = (k_pre - 1) / cur) by
    (apply Z.quot_div_nonneg; lia).
  rewrite Hinner.
  rewrite Z.quot_div_nonneg by lia.
  unfold QuotientBlock.
  intros num Hnum.
  pose proof
    (quotient_block_plateau__solver_quotient_routes
       (k_pre - 1) cur ltac:(lia) ltac:(lia) Hqpos) as [_ Hplateau].
  apply Hplateau.
  exact Hnum.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_4 : solver_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_5 : solver_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst z.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  assert (Hqnonneg : 0 <= (k_pre - 1) / cur) by
    (apply Z.div_pos; lia).
  assert (Hqpos : 0 < (k_pre - 1) / cur) by lia.
  assert (Hinner : (k_pre - 1) ÷ cur = (k_pre - 1) / cur) by
    (apply Z.quot_div_nonneg; lia).
  rewrite Hinner.
  rewrite Z.quot_div_nonneg by lia.
  exact (proj1
    (quotient_block_plateau__solver_quotient_routes
       (k_pre - 1) cur ltac:(lia) ltac:(lia) Hqpos)).
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH4.
  apply candy_prefix_to_phase0_block__solver_quotient_routes.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst z.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  rewrite Z.quot_div_nonneg by lia.
  rewrite PreH2.
  apply quotient_block_zero__solver_quotient_routes; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst x.
  eapply candy_phase2_block_to_prefix__solver_init_close; eauto.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst R.
  eapply candy_max_transport__solver_final_semantics.
  - lia.
  - lia.
  - lia.
  - lia.
  - split; [exact PreH12 | exact PreH13].
  - rewrite <- Z.rem_mod_nonneg by lia. exact PreH2.
  - assumption.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
