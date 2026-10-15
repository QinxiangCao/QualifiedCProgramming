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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P089_1891E_brukhovich_and_exams_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P089_1891E_brukhovich_and_exams_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P089_1891E_brukhovich_and_exams_lib.
Local Open Scope sac.

Lemma proof_of_gcdll_entail_wit_1 : gcdll_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (Z.gcd a_pre b_pre).
  unfold GcdResult.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbpos : 0 < b) by lia.
  pose proof (Z.rem_bound_pos a b PreH1 Hbpos) as Hrem.
  assert (Hgcd : GcdResult b (Z.rem a b) g_2).
  {
    rewrite Z.rem_mod_nonneg by lia.
    unfold GcdResult in *.
    rewrite Z.gcd_comm.
    rewrite Z.gcd_mod by lia.
    rewrite Z.gcd_comm.
    exact PreH5.
  }
  Exists g_2.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; (assumption || lia).
Qed.

Lemma proof_of_gcdll_return_wit_1_split_goal_1 : gcdll_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdResult in *.
  subst b.
  rewrite Z.gcd_0_r in PreH5.
  rewrite Z.abs_eq in PreH5 by lia.
  lia.
Qed.

Lemma proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gcdll_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_41_split_goal_1 : solver_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH21 by lia.
  pose proof (pair_savings_scan_int_bound__pair_scan_safety
    values (i + 1) two run scan_savings ltac:(lia) PreH22).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_41_split_goal_2 : solver_safety_wit_41_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_pos run 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_47_split_goal_1 : solver_safety_wit_47_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH18 by lia.
  pose proof (pair_savings_scan_int_bound__pair_scan_safety
    values (i + 1) two run scan_savings ltac:(lia) PreH19).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_47_split_goal_2 : solver_safety_wit_47_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_pos run 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_47_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_47_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_50_split_goal_1 : solver_safety_wit_50_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH19 by lia.
  pose proof (pair_savings_scan_int_bound__pair_scan_safety
    values (i + 1) two run scan_savings ltac:(lia) PreH20).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_50_split_goal_2 : solver_safety_wit_50_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_pos run 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_50_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_50_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_89_split_goal_1 : solver_safety_wit_89_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i by lia.
  unfold OptimizationSafetyBounds in PreH16.
  destruct PreH16 as [_ [Hpositive _]].
  pose proof (forall_positive_lowerbound__greedy_transition _ Hpositive)
    as Hblocks_lower.
  pose proof (ListLib.lowerbound_perm 1 blocks sorted PreH13 Hblocks_lower)
    as Hsorted_lower.
  pose proof (ListLib.lowerbound_Znth 1 sorted i Hsorted_lower ltac:(lia))
    as Hcurrent_positive.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_89_split_goal_2 : solver_safety_wit_89_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_89 : solver_safety_wit_89.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_89_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_89_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_90_split_goal_1 : solver_safety_wit_90_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i by lia.
  unfold OptimizationSafetyBounds in PreH16.
  destruct PreH16 as [_ [Hpositive _]].
  pose proof (forall_positive_lowerbound__greedy_transition _ Hpositive)
    as Hblocks_lower.
  pose proof (ListLib.lowerbound_perm 1 blocks sorted PreH13 Hblocks_lower)
    as Hsorted_lower.
  pose proof (ListLib.lowerbound_Znth 1 sorted i Hsorted_lower ltac:(lia))
    as Hcurrent_positive.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_90_split_goal_2 : solver_safety_wit_90_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  replace (i - 0) with i by lia.
  replace (i - 0) with i in PreH1 by lia.
  assert (Huse_two : use <= two).
  {
    unfold MinValue in PreH17.
    rewrite PreH17.
    apply Z.le_min_r.
  }
  pose proof
    (greedy_block_state_step__greedy_loop
      sorted blocks i base_sad two use (k_pre - use) k sad
      PreH20 ltac:(lia) PreH13 PreH16 Huse_two PreH26 PreH1)
    as [_ [Hnew_sad_nonnegative _]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_90 : solver_safety_wit_90.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_90_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_90_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AllOnePrefix.
  left.
  split; [reflexivity |].
  intros j Hj.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst n_pre.
  apply PreH4.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AllOnePrefix in *.
  destruct PreH12 as [[Hflag Hall] | [Hflag [j [Hj Hnonone]]]].
  - right.
    split; [reflexivity |].
    exists i.
    split; [lia | exact PreH1].
  - right.
    split; [reflexivity |].
    exists j.
    split; [lia | exact Hnonone].
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AllOnePrefix in *.
  destruct PreH12 as [[Hflag Hall] | [Hflag [j [Hj Hnonone]]]].
  - left.
    split; [exact Hflag |].
    intros q Hq.
    destruct (Z.eq_dec q i) as [-> | Hneq].
    + exact PreH1.
    + apply Hall. lia.
  - right.
    split; [exact Hflag |].
    exists j.
    split; [lia | exact Hnonone].
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i allone.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (coprime_prefix_count_extend_hit__coprime_scan
    values i sad PreH12 PreH16).
  unfold AdjacentCoprime, GcdResult in *.
  split; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (coprime_prefix_count_extend_miss__coprime_scan
    values i sad PreH12 PreH16).
  unfold AdjacentCoprime, GcdResult in *.
  intros [_ Hgcd].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i_4 = n_pre - 1) by lia.
  assert (Hcop : CoprimeEdgePrefixCount values (n_pre - 1) sad).
  { rewrite <- Hi. exact PreH14. }
  assert (Hpair : PairSavingsPrefix values 0 two).
  { rewrite PreH8. apply pair_savings_prefix_zero__coprime_scan. }
  Right.
  Exists 0.
  split_pure_spatial.
  - cancel (((&( "i" ))) # Int |-> 0).
    cancel (Int64Array.full a_pre n_pre values).
  - split_pures.
    all: dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PairSavingsScan.
  split.
  - rewrite Z.quot_0_l by lia.
    rewrite Z.div_0_l by lia.
    lia.
  - split; [lia |].
    assert (Hprefix : PairSavingsPrefix values (i + 1) two).
    {
      eapply pair_savings_prefix_extend_isolated_nonone__pair_scan_entry.
      - lia.
      - right. exact PreH17.
      - exact PreH18.
    }
    rewrite Z.quot_0_l by lia.
    replace (two + 0) with two by lia.
    exact Hprefix.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_2 : solver_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PairRunSuffix; simpl.
  replace (i + 1 - 0 - 1) with i by lia.
  split; [lia |].
  split.
  - intros j Hj. assert (j = i) by lia. subst j. exact PreH1.
  - split.
    + intros j Hj. lia.
    + right; left. exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_3 : solver_entail_wit_6_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  unfold PairSavingsScan.
  split.
  - rewrite Z.quot_0_l by lia.
    rewrite Z.div_0_l by lia.
    lia.
  - split; [lia |].
    assert (Hprefix : PairSavingsPrefix values (0 + 1) two).
    {
      eapply pair_savings_prefix_extend_isolated_nonone__pair_scan_entry.
      - lia.
      - left. reflexivity.
      - exact PreH18.
    }
    rewrite Z.quot_0_l by lia.
    replace (two + 0) with two by lia.
    exact Hprefix.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_2 : solver_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  unfold PairRunSuffix; simpl.
  split; [lia |].
  split.
  - intros j Hj. assert (j = 0) by lia. subst j. exact PreH1.
  - split.
    + intros j Hj. lia.
    + left. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_3 : solver_entail_wit_6_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hedge : AdjacentCoprime values i).
  {
    unfold AdjacentCoprime, GcdResult in *.
    split; lia.
  }
  assert (Hbound : i + 1 < Zlength values) by lia.
  pose proof (pair_savings_scan_step__pair_scan_steps
    values i two run scan_savings_2 PreH15 Hbound PreH3 PreH21
    PreH20 PreH22) as Hstep.
  exact ((proj1 Hstep) Hedge).
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hedge : AdjacentCoprime values i).
  {
    unfold AdjacentCoprime, GcdResult in *.
    split; lia.
  }
  eapply pair_run_suffix_coprime_step__pair_scan_steps;
    eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbreak : ~ AdjacentCoprime values i).
  {
    unfold AdjacentCoprime, GcdResult in *.
    intros [_ Hedge]. lia.
  }
  assert (Hbound : i + 1 < Zlength values) by lia.
  pose proof (pair_savings_scan_step__pair_scan_steps
    values i two run scan_savings_2 PreH15 Hbound PreH3 PreH21
    PreH20 PreH22) as Hstep.
  exact ((proj2 Hstep) Hbreak).
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbreak : ~ AdjacentCoprime values i).
  {
    unfold AdjacentCoprime, GcdResult in *.
    intros [_ Hedge]. lia.
  }
  apply pair_run_suffix_restart_noncoprime__pair_scan_transitions.
  - lia.
  - exact PreH3.
  - exact Hbreak.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_3 : solver_entail_wit_7_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hq : 0 <= run ÷ 2).
  { apply Z.quot_pos; lia. }
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i_4 + 1 = n_pre) by lia.
  pose proof (pair_scan_finish__pair_scan_exit
    values (i_4 + 1) two run scan_savings ltac:(lia) PreH19)
    as Hfinish.
  destruct Hfinish as [Hvalue [Hprefix [Hnonneg Htwice]]].
  Left. Right.
  split_pure_spatial.
  - rewrite <- Hi. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: rewrite <- PreH18; try rewrite <- Hi; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (pair_scan_finish__pair_scan_exit
    values (i_4 + 1) two run scan_savings ltac:(lia) PreH20)
    as Hfinish.
  destruct Hfinish as [Hvalue [Hprefix [Hnonneg Htwice]]].
  Left. Left. Right. Exists (i_4 + 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: rewrite <- PreH19; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (pair_prefix_cross_one__pair_scan_exit
    values i_4 two PreH1 PreH18) as Hprefix.
  Left. Left. Left. Exists (i_4 + 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    replace (i_4 + 1 - 1) with i_4 by lia. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (pair_prefix_cross_one__pair_scan_exit
    values i_4 two PreH1 PreH18) as Hprefix.
  Left. Left. Left. Exists (i_4 + 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    replace (i_4 + 1 - 1) with i_4 by lia. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (pair_prefix_cross_one__pair_scan_exit
    values i_4 two PreH1 PreH18) as Hprefix.
  Left. Left. Left. Exists (i_4 + 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    replace (i_4 + 1 - 1) with i_4 by lia. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnonone : exists j,
    0 <= j < Zlength values /\ Znth j values 0 <> 1).
  {
    unfold AllOnePrefix in PreH8.
    destruct PreH8 as [[Hflag _] | [_ Hexists]]; [lia |].
    rewrite <- PreH2. exact Hexists.
  }
  eapply canonical_certificate_nil_from_scans__certificate_bootstrap.
  - intros j Hj. exact (proj1 (PreH6 j ltac:(lia))).
  - exact Hnonone.
  - rewrite <- PreH2. exact PreH9.
  - rewrite <- PreH2. replace n_pre with i by lia. exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_2 : solver_entail_wit_9_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace n_pre with i by lia.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_3 : solver_entail_wit_9_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  unfold Znth in PreH16.
  rewrite nth_overflow in PreH16.
  - lia.
  - rewrite PreH2, Zlength_correct, Nat2Z.id.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_2 : solver_entail_wit_9_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace n_pre with i by lia.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_3 : solver_entail_wit_9_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9_3_split_goal_1 : solver_entail_wit_9_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnonone : exists j,
    0 <= j < Zlength values /\ Znth j values 0 <> 1).
  {
    unfold AllOnePrefix in PreH8.
    destruct PreH8 as [[Hflag _] | [_ Hexists]]; [lia |].
    rewrite <- PreH2. exact Hexists.
  }
  eapply canonical_certificate_nil_from_scans__certificate_bootstrap.
  - intros j Hj. exact (proj1 (PreH6 j ltac:(lia))).
  - exact Hnonone.
  - rewrite <- PreH2. exact PreH9.
  - rewrite <- PreH2. exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_9_3_split_goal_2 : solver_entail_wit_9_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Right.
  Exists (@nil Z) 0.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval n_pre).
  rewrite (IntArray.full_empty retval 0).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial;
      try reflexivity;
      try assumption;
      try lia.
    + apply canonical_interior_one_run_prefix_empty__block_scan_init.
    + eapply joint_pair_block_empty__block_scan_init.
      * rewrite <- PreH2. exact PreH9.
      * rewrite <- PreH2. exact PreH10.
      * exact PreH14.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Right.
  Exists blocks_2.
  split_pure_spatial.
  - cancel. cancel.
  - split_pures.
    all: dump_pre_spatial;
      try reflexivity;
      try assumption;
      try lia.
    unfold CanonicalOneRunScanState.
    split; [assumption |].
    intros j Hj. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists blocks_2.
  split_pure_spatial.
  - cancel. cancel.
  - split_pures.
    all: dump_pre_spatial;
      try reflexivity;
      try assumption;
      try lia.
    unfold CanonicalOneRunScanState.
    split; [assumption |].
    intros j Hj. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists blocks_2.
  split_pure_spatial.
  - cancel. cancel.
  - split_pures.
    all: dump_pre_spatial;
      try reflexivity;
      try assumption;
      try lia;
      eauto using canonical_one_run_scan_state_step__block_scan_init.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Right.
  Exists blocks_2.
  split_pure_spatial.
  - cancel. cancel.
  - split_pures.
    all: dump_pre_spatial;
      try reflexivity;
      try assumption;
      try lia;
      eauto using canonical_one_run_scan_state_step__block_scan_init.
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcanonical : CanonicalInteriorOneRunPrefix values i_4
    (blocks_2 ++ (cons (i_4 - l) nil))).
  { eapply canonical_run_append_closed__block_scan_steps_a.
    - split; [lia |]. assert (l <> i_4) by congruence. lia.
    - lia.
    - exact PreH19.
    - exact PreH3.
    - exact PreH23. }
  assert (Hjoint : JointPairBlockPrefix values i_4 sad two
    (blocks_2 ++ (cons (i_4 - l) nil))).
  { eapply joint_run_completed_append__block_scan_steps_a.
    - split; [lia |]. assert (l <> i_4) by congruence. lia.
    - lia.
    - exact PreH19.
    - exact PreH3.
    - exact PreH23.
    - exact PreH24.
    - exact PreH25. }
  pose proof (canonical_exam_block_collection_certificate_append
    values sad two blocks_2 (i_4 - l) PreH25) as Hcert.
  Left. Right.
  Exists (blocks_2 ++ (cons (i_4 - l) nil)) i_4.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 (oc + 1)
      (blocks_2 ++ (cons (i_4 - l) nil))).
    cancel (IntArray.undef_seg ones (oc + 1) n_pre).
    cancel (&( "i") # Int |-> i_4).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    + assert (l <> i_4) by congruence. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hl : l = 0) by lia. subst l.
  assert (Hcanonical : CanonicalInteriorOneRunPrefix values i_4 blocks_2).
  { eapply canonical_run_leading_close__block_scan_steps_a; eauto; lia. }
  assert (Hjoint : JointPairBlockPrefix values i_4 sad two blocks_2).
  { eapply joint_run_close_no_record__block_scan_steps_a; eauto; lia. }
  Left. Left. Right.
  Exists blocks_2 i_4.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc blocks_2).
    cancel (IntArray.undef_seg ones oc n_pre).
    cancel (&( "i") # Int |-> i_4).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: lia.
Qed.

Lemma proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst l.
  assert (Hcanonical : CanonicalInteriorOneRunPrefix values i_4 blocks_2).
  { eapply canonical_run_leading_close__block_scan_steps_a; eauto; lia. }
  assert (Hjoint : JointPairBlockPrefix values i_4 sad two blocks_2).
  { eapply joint_run_close_no_record__block_scan_steps_a; eauto; lia. }
  Left. Right.
  Exists blocks_2 i_4.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc blocks_2).
    cancel (IntArray.undef_seg ones oc n_pre).
    cancel (&( "i") # Int |-> i_4).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: lia.
Qed.

Lemma proof_of_solver_entail_wit_13_4 : solver_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst l.
  assert (Hi : i_4 = n_pre) by lia. subst i_4.
  assert (Hcanonical : CanonicalInteriorOneRunPrefix values n_pre blocks_2).
  { exact (canonical_run_leading_close__block_scan_steps_a
      values 0 n_pre blocks_2 ltac:(lia) ltac:(lia) PreH21). }
  assert (Hjoint : JointPairBlockPrefix values n_pre sad two blocks_2).
  { exact (joint_run_close_no_record__block_scan_steps_a
      values 0 n_pre sad two blocks_2 ltac:(lia) ltac:(left; lia)
      PreH21 PreH22). }
  Left. Right.
  Exists blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc blocks_2).
    cancel (IntArray.undef_seg ones oc n_pre).
    cancel (&( "i") # Int |-> n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: lia.
Qed.

Lemma proof_of_solver_entail_wit_13_5 : solver_entail_wit_13_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (l = 0) by lia. subst l.
  assert (i_4 = n_pre) by lia. subst i_4.
  assert (Hprofile : CanonicalInteriorOneRunPrefix values n_pre blocks_2).
  {
    eapply canonical_run_close_boundary_no_record__block_scan_steps_b
      with (lo := 0); eauto; lia.
  }
  assert (Hjoint : JointPairBlockPrefix values n_pre sad two blocks_2).
  {
    eapply joint_pair_block_close_boundary_no_record__block_scan_steps_b
      with (lo := 0); eauto; lia.
  }
  Left. Right.
  Exists blocks_2.
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_13_6 : solver_entail_wit_13_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i_4 = n_pre) by lia. subst i_4.
  assert (Hprofile : CanonicalInteriorOneRunPrefix values n_pre blocks_2).
  {
    eapply canonical_run_close_boundary_no_record__block_scan_steps_b
      with (lo := l); eauto; lia.
  }
  assert (Hjoint : JointPairBlockPrefix values n_pre sad two blocks_2).
  {
    eapply joint_pair_block_close_boundary_no_record__block_scan_steps_b
      with (lo := l); eauto; lia.
  }
  Left. Right.
  Exists blocks_2.
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_13_7 : solver_entail_wit_13_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (canonical_run_skip_nonone__block_scan_steps_b
      values i_4 blocks_2 PreH19 PreH1) as Hprofile.
  pose proof
    (joint_pair_block_skip_nonone__block_scan_steps_b
      values i_4 sad two blocks_2 PreH19 PreH20 PreH1) as Hjoint.
  Left. Left. Left.
  Exists blocks_2 (i_4 + 1).
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; try lia.
    replace (i_4 + 1 - 1) with i_4 by lia.
    exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_13_8 : solver_entail_wit_13_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (canonical_run_skip_nonone__block_scan_steps_b
      values i_4 blocks_2 PreH19 PreH1) as Hprofile.
  pose proof
    (joint_pair_block_skip_nonone__block_scan_steps_b
      values i_4 sad two blocks_2 PreH19 PreH20 PreH1) as Hjoint.
  Left. Left. Left.
  Exists blocks_2 (i_4 + 1).
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; try lia.
    replace (i_4 + 1 - 1) with i_4 by lia.
    exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_13_9 : solver_entail_wit_13_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (canonical_run_skip_nonone__block_scan_steps_b
      values i_4 blocks_2 PreH19 PreH1) as Hprofile.
  pose proof
    (joint_pair_block_skip_nonone__block_scan_steps_b
      values i_4 sad two blocks_2 PreH19 PreH20 PreH1) as Hjoint.
  Left. Left. Left.
  Exists blocks_2 (i_4 + 1).
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; try lia.
    replace (i_4 + 1 - 1) with i_4 by lia.
    exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH2 in PreH16, PreH17, PreH18.
  pose proof (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH18 PreH20) as Hcertificate.
  assert (Hsad : ExamSadness values sad).
  {
    apply coprime_edge_full_is_exam_sadness.
    exact PreH16.
  }
  pose proof (canonical_interior_one_run_prefix_projects
    values (Zlength values) blocks_2 PreH18) as Hblocks.
  pose proof (exam_joint_optimization_certificate_projects
    values sad two blocks_2 Hsad PreH17 Hblocks Hcertificate) as Hprojects.
  exact (proj1 Hprojects).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH2 in PreH16, PreH17, PreH18.
  pose proof (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH18 PreH20) as Hcertificate.
  assert (Hsad : ExamSadness values sad).
  {
    apply coprime_edge_full_is_exam_sadness.
    exact PreH16.
  }
  pose proof (canonical_interior_one_run_prefix_projects
    values (Zlength values) blocks_2 PreH18) as Hblocks.
  pose proof (exam_joint_optimization_certificate_projects
    values sad two blocks_2 Hsad PreH17 Hblocks Hcertificate) as Hprojects.
  exact (proj2 Hprojects).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH2 in PreH18.
  exact (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH18 PreH20).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_5 : solver_entail_wit_14_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_6 : solver_entail_wit_14_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH2 in PreH16, PreH17, PreH18.
  pose proof (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH18 PreH20) as Hcertificate.
  assert (Hsad : ExamSadness values sad).
  {
    apply coprime_edge_full_is_exam_sadness.
    exact PreH16.
  }
  pose proof (canonical_interior_one_run_prefix_projects
    values (Zlength values) blocks_2 PreH18) as Hblocks.
  pose proof (exam_joint_optimization_certificate_projects
    values sad two blocks_2 Hsad PreH17 Hblocks Hcertificate) as Hprojects.
  exact (proj1 Hprojects).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH2 in PreH16, PreH17, PreH18.
  pose proof (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH18 PreH20) as Hcertificate.
  assert (Hsad : ExamSadness values sad).
  {
    apply coprime_edge_full_is_exam_sadness.
    exact PreH16.
  }
  pose proof (canonical_interior_one_run_prefix_projects
    values (Zlength values) blocks_2 PreH18) as Hblocks.
  pose proof (exam_joint_optimization_certificate_projects
    values sad two blocks_2 Hsad PreH17 Hblocks Hcertificate) as Hprojects.
  exact (proj2 Hprojects).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH2 in PreH18.
  exact (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH18 PreH20).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_4 : solver_entail_wit_14_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_5 : solver_entail_wit_14_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_6 : solver_entail_wit_14_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_1 : solver_entail_wit_14_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH2 in PreH15, PreH16, PreH17.
  pose proof (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH17 PreH19) as Hcertificate.
  assert (Hsad : ExamSadness values sad).
  {
    apply coprime_edge_full_is_exam_sadness.
    exact PreH15.
  }
  pose proof (canonical_interior_one_run_prefix_projects
    values (Zlength values) blocks_2 PreH17) as Hblocks.
  pose proof (exam_joint_optimization_certificate_projects
    values sad two blocks_2 Hsad PreH16 Hblocks Hcertificate) as Hprojects.
  exact (proj1 Hprojects).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_2 : solver_entail_wit_14_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH2 in PreH15, PreH16, PreH17.
  pose proof (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH17 PreH19) as Hcertificate.
  assert (Hsad : ExamSadness values sad).
  {
    apply coprime_edge_full_is_exam_sadness.
    exact PreH15.
  }
  pose proof (canonical_interior_one_run_prefix_projects
    values (Zlength values) blocks_2 PreH17) as Hblocks.
  pose proof (exam_joint_optimization_certificate_projects
    values sad two blocks_2 Hsad PreH16 Hblocks Hcertificate) as Hprojects.
  exact (proj2 Hprojects).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_3 : solver_entail_wit_14_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH2 in PreH17.
  exact (canonical_exam_block_collection_certificate_full_projects
    values sad two blocks_2 PreH17 PreH19).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_4 : solver_entail_wit_14_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + replace (sad - 2 * k_pre + 2 * k_pre) with sad by lia.
      assumption.
    + replace (sad - 2 * k_pre + 2 * k_pre) with sad by lia.
      assumption.
    + unfold MinValue.
      rewrite Z.min_l by lia.
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + replace (sad - 2 * two + 2 * two) with sad by lia.
      assumption.
    + replace (sad - 2 * two + 2 * two) with sad by lia.
      assumption.
    + unfold MinValue.
      rewrite Z.min_r by lia.
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Huse_le_two : use <= two).
  {
    unfold MinValue in PreH15.
    rewrite PreH15.
    apply Z.le_min_r.
  }
  pose proof PreH13 as Hsummary_parts.
  unfold ExamOptimizationSummary in Hsummary_parts.
  destruct Hsummary_parts as [Hbase_sad _].
  pose proof (exam_sadness_bounds__final_result values (sad + 2 * use)
    ltac:(lia) Hbase_sad) as Hbase_bounds.
  pose proof PreH14 as Hsafe_parts.
  unfold OptimizationSafetyBounds in Hsafe_parts.
  destruct Hsafe_parts as [Htwo_nonneg [Hblocks_pos Htotal]].
  pose proof (forall_positive_lowerbound__greedy_transition _ Hblocks_pos)
    as Hblocks_lower.
  pose proof (map_succ_lowerbound_nonnegative__greedy_transition _ Hblocks_lower)
    as Hmap_lower.
  pose proof (sum_nonnegative_lowerbound__greedy_transition _ Hmap_lower)
    as Hsum_nonnegative.
  assert (Hsad_nonnegative : 0 <= sad) by lia.
  assert (Hsad_upper : sad <= n_pre) by lia.
  assert (Hzero :
    GreedyBlockState sorted_2 0 (k_pre - use)
      ((sad + 2 * use) - 2 * use) k sad).
  {
    replace ((sad + 2 * use) - 2 * use) with sad by lia.
    rewrite PreH16.
    apply greedy_block_state_zero__greedy_setup.
  }
  Exists (sad + 2 * use) sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_18 : solver_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Huse_le_two : use <= two).
  {
    unfold MinValue in PreH17.
    rewrite PreH17.
    apply Z.le_min_r.
  }
  replace (i - 0) with i in PreH1 by lia.
  pose proof
    (greedy_block_state_step__greedy_transition
      sorted_2 blocks_2 i base_sad_2 two use (k_pre - use) k sad
      PreH20 ltac:(lia) PreH13 PreH16 Huse_le_two PreH26 PreH1)
    as Hstep.
  destruct Hstep as [Hcurrent_positive [Hnew_sad_nonnegative Hnew_state]].
  Exists base_sad_2 sorted_2 blocks_2.
  replace (i - 0) with i by lia.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_19_1 : solver_entail_wit_19_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH16 as Hsummary.
  unfold ExamOptimizationSummary in Hsummary.
  destruct Hsummary as [_ [_ [_ Hsummary]]].
  assert (Hstop : i = Zlength sorted_2 \/ Znth i sorted_2 0 > k).
  { left. lia. }
  assert (Hfinal : FinalBudgetResult k sad (sad - sad)).
  {
    apply greedy_final_result_from_scalar_updates__greedy_loop.
    right. split; lia.
  }
  assert (Hspec : Spec k_pre values (sad - sad)).
  {
    eapply Hsummary.
    - lia.
    - exact PreH14.
    - exact PreH15.
    - exact PreH18.
    - exact PreH27.
    - exact Hstop.
    - exact Hfinal.
  }
  Exists base_sad_2 sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_19_2 : solver_entail_wit_19_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in PreH3 by lia.
  pose proof PreH17 as Hsummary.
  unfold ExamOptimizationSummary in Hsummary.
  destruct Hsummary as [_ [_ [_ Hsummary]]].
  assert (Hstop : i = Zlength sorted_2 \/ Znth i sorted_2 0 > k).
  { right. exact PreH3. }
  assert (Hfinal : FinalBudgetResult k sad (sad - sad)).
  {
    apply greedy_final_result_from_scalar_updates__greedy_loop.
    right. split; lia.
  }
  assert (Hspec : Spec k_pre values (sad - sad)).
  {
    eapply Hsummary.
    - lia.
    - exact PreH15.
    - exact PreH16.
    - exact PreH19.
    - exact PreH28.
    - exact Hstop.
    - exact Hfinal.
  }
  Exists base_sad_2 sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_19_3 : solver_entail_wit_19_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH16 as Hsummary.
  unfold ExamOptimizationSummary in Hsummary.
  destruct Hsummary as [Hbase_exam [_ [_ Hsummary]]].
  pose proof (exam_sadness_bounds__final_result values base_sad_2
    ltac:(lia) Hbase_exam) as Hbase_bounds.
  pose proof PreH17 as Hsafety.
  unfold OptimizationSafetyBounds in Hsafety.
  destruct Hsafety as [_ [Hpositive _]].
  pose proof
    (greedy_block_state_sadness_upper_bound__greedy_loop
      sorted_2 blocks_2 i (k_pre - use) (base_sad_2 - 2 * use)
      k sad PreH14 Hpositive PreH27) as Hsadness_upper.
  assert (Hresult_strict : sad - k < n_pre) by lia.
  assert (Hstop : i = Zlength sorted_2 \/ Znth i sorted_2 0 > k).
  { left. lia. }
  assert (Hfinal : FinalBudgetResult k sad (sad - k)).
  {
    apply greedy_final_result_from_scalar_updates__greedy_loop.
    left. split; lia.
  }
  assert (Hspec : Spec k_pre values (sad - k)).
  {
    eapply Hsummary.
    - lia.
    - exact PreH14.
    - exact PreH15.
    - exact PreH18.
    - exact PreH27.
    - exact Hstop.
    - exact Hfinal.
  }
  Exists base_sad_2 sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_19_4 : solver_entail_wit_19_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in PreH3 by lia.
  pose proof PreH17 as Hsummary.
  unfold ExamOptimizationSummary in Hsummary.
  destruct Hsummary as [Hbase_exam [_ [_ Hsummary]]].
  pose proof (exam_sadness_bounds__final_result values base_sad_2
    ltac:(lia) Hbase_exam) as Hbase_bounds.
  pose proof PreH18 as Hsafety.
  unfold OptimizationSafetyBounds in Hsafety.
  destruct Hsafety as [_ [Hpositive _]].
  pose proof
    (greedy_block_state_sadness_upper_bound__greedy_loop
      sorted_2 blocks_2 i (k_pre - use) (base_sad_2 - 2 * use)
      k sad PreH15 Hpositive PreH28) as Hsadness_upper.
  assert (Hresult_strict : sad - k < n_pre) by lia.
  assert (Hstop : i = Zlength sorted_2 \/ Znth i sorted_2 0 > k).
  { right. exact PreH3. }
  assert (Hfinal : FinalBudgetResult k sad (sad - k)).
  {
    apply greedy_final_result_from_scalar_updates__greedy_loop.
    left. split; lia.
  }
  assert (Hspec : Spec k_pre values (sad - k)).
  {
    eapply Hsummary.
    - lia.
    - exact PreH15.
    - exact PreH16.
    - exact PreH19.
    - exact PreH28.
    - exact Hstop.
    - exact Hfinal.
  }
  Exists base_sad_2 sorted_2 blocks_2.
  split_pure_spatial.
  - cancel (Int64Array.full a_pre n_pre values).
    cancel (IntArray.seg ones 0 oc sorted_2).
    cancel (IntArray.undef_seg ones oc n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace 0 with (Zlength values - k_pre) by lia.
  apply all_one_exam_optimum__allone_returns.
  - lia.
  - unfold AllOnePrefix in PreH12.
    destruct PreH12 as [[_ Hall] | [Hflag _]].
    + intros j Hj. apply Hall. lia.
    + lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (n_pre - k_pre) with (Zlength values - k_pre) by lia.
  apply all_one_exam_optimum__allone_returns.
  - lia.
  - unfold AllOnePrefix in PreH12.
    destruct PreH12 as [[_ Hall] | [Hflag _]].
    + intros j Hj. apply Hall. lia.
    + lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.
