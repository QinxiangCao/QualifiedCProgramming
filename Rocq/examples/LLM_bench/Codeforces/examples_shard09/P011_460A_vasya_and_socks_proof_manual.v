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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P011_460A_vasya_and_socks_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P011_460A_vasya_and_socks_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_0_l by lia.
  lia.
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
  rewrite (Z.quot_div_nonneg days m_pre ltac:(lia) ltac:(lia)).
  rewrite (Z.quot_div_nonneg (days + 1) m_pre ltac:(lia) ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (days + 1) m_pre ltac:(lia) ltac:(lia)) in PreH1.
  pose proof (Z.mod_pos_bound days m_pre ltac:(lia)) as Hmod_days.
  pose proof (Z.div_mod (days + 1) m_pre ltac:(lia)) as Hdiv_next.
  assert (Hquot : (days + 1) / m_pre - 1 = days / m_pre).
  { apply Z.div_unique_pos with (r := m_pre - 1).
    - lia.
    - nia. }
  nia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (Z.quot_div_nonneg days m_pre ltac:(lia) ltac:(lia)) in PreH11.
  pose proof (Z.mod_pos_bound days m_pre ltac:(lia)) as Hmod_days.
  pose proof (Z.div_mod days m_pre ltac:(lia)) as Hdiv_days.
  pose proof (Z.div_pos days m_pre ltac:(lia) ltac:(lia)) as Hdiv_nonneg.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (Z.quot_div_nonneg days m_pre ltac:(lia) ltac:(lia)).
  rewrite (Z.quot_div_nonneg (days + 1) m_pre ltac:(lia) ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (days + 1) m_pre ltac:(lia) ltac:(lia)) in PreH1.
  pose proof (Z.mod_pos_bound days m_pre ltac:(lia)) as Hmod_days.
  pose proof (Z.div_mod days m_pre ltac:(lia)) as Hdiv_days.
  destruct (Z.eq_dec (days mod m_pre + 1) m_pre) as [Hwrap | Hnowrap].
  - assert (Hzero : (days + 1) mod m_pre = 0).
    { symmetry. apply Z.mod_unique_pos with (q := days / m_pre + 1).
      + lia.
      + nia. }
    contradiction.
  - assert (Hbound : 0 <= days mod m_pre + 1 < m_pre) by lia.
    assert (Hquot : days / m_pre = (days + 1) / m_pre).
    { apply Z.div_unique_pos with (r := days mod m_pre + 1).
      + exact Hbound.
      + nia. }
    nia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (Z.quot_div_nonneg days m_pre ltac:(lia) ltac:(lia)) in PreH11.
  pose proof (Z.mod_pos_bound days m_pre ltac:(lia)) as Hmod_days.
  pose proof (Z.div_mod days m_pre ltac:(lia)) as Hdiv_days.
  pose proof (Z.div_pos days m_pre ltac:(lia) ltac:(lia)) as Hdiv_nonneg.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hn : n = 0) by lia.
  assert (Hquot : days ÷ m_pre = days / m_pre).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hdiv : 0 <= days / m_pre).
  { apply Z_div_nonneg_nonneg; lia. }
  assert (Hdays : 1 <= days) by lia.
  unfold Spec.
  split.
  - lia.
  - split.
    + intros d Hd.
      rewrite <- Z.quot_div_nonneg by lia.
      apply PreH11.
      exact Hd.
    + rewrite Hquot in PreH10.
      lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
