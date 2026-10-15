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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P073_1799D2_hot_start_up_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P073_1799D2_hot_start_up_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH10 as [Hprog_lo Hprog_hi].
  specialize (PreH11 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH11 as [[Hhot_lo Hhot_cold] Hcold_hi].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH10 as [Hprog_lo Hprog_hi].
  specialize (PreH11 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH11 as [[Hhot_lo Hhot_cold] Hcold_hi].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH10 as [Hprog_lo Hprog_hi].
  specialize (PreH11 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH11 as [[Hhot_lo Hhot_cold] Hcold_hi].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH10 as [Hprog_lo Hprog_hi].
  specialize (PreH11 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH11 as [[Hhot_lo Hhot_cold] Hcold_hi].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH11 as [Hprog_lo Hprog_hi].
  specialize (PreH12 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH12 as [[Hhot_lo Hhot_cold] Hcold_hi].
  specialize (PreH23 (Znth i prog 0) ltac:(lia)).
  destruct PreH23 as [PreH23 | [PreH23 PreH25]]; [lia |].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH11 as [Hprog_lo Hprog_hi].
  specialize (PreH12 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH12 as [[Hhot_lo Hhot_cold] Hcold_hi].
  specialize (PreH23 (Znth i prog 0) ltac:(lia)).
  destruct PreH23 as [PreH23 | [PreH23 PreH25]]; [lia |].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH11 as [Hprog_lo Hprog_hi].
  specialize (PreH12 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH12 as [[Hhot_lo Hhot_cold] Hcold_hi].
  specialize (PreH23 (Znth i prog 0) ltac:(lia)).
  destruct PreH23 as [PreH23 | [PreH23 PreH25]]; [lia |].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH11 as [Hprog_lo Hprog_hi].
  specialize (PreH12 (Znth i prog 0 - 1) ltac:(lia)).
  destruct PreH12 as [[Hhot_lo Hhot_cold] Hcold_hi].
  specialize (PreH23 (Znth i prog 0) ltac:(lia)).
  destruct PreH23 as [PreH23 | [PreH23 PreH25]]; [lia |].
  repeat rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_21_split_goal_1 : solver_safety_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_21_split_goal_2 : solver_safety_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_21_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_21_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hprog.
  pose proof (PreH13 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH11 i ltac:(lia)) as Hprog.
  pose proof (PreH12 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH11 i ltac:(lia)) as Hprog.
  pose proof (PreH12 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH11 i ltac:(lia)) as Hprog.
  pose proof (PreH12 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH11 i ltac:(lia)) as Hprog.
  pose proof (PreH12 (Znth i prog 0 - 1) ltac:(lia)) as Hcost.
  destruct Hprog as [Hproglo Hproghi].
  destruct Hcost as [[Hcostlo Hcostmid] Hcosthi].
  dump_pre_spatial.
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  specialize (PreH24 (Znth i prog 0) ltac:(lia)).
  rewrite !Znth_cons by lia.
  destruct PreH13 as [[Hhot_lo Hhot_le_cold] Hcold_hi].
  destruct PreH24 as [Hinf | [Hdp_lo Hdp_hi]].
  - lia.
  - dump_pre_spatial.
    lia.
Qed.

Lemma proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite !Znth_cons by lia.
  destruct PreH13 as [[Hhot_lo Hhot_le_cold] Hcold_hi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_31_split_goal_1 : solver_safety_wit_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  specialize (PreH12 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite !Znth_cons by lia.
  destruct PreH12 as [[Hhot_lo Hhot_le_cold] Hcold_hi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_31_split_goal_2 : solver_safety_wit_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  specialize (PreH12 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite !Znth_cons by lia.
  destruct PreH12 as [[Hhot_lo Hhot_le_cold] Hcold_hi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_31_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_31_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH13.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = k_pre + 1) by lia.
  assert (Hinitlen : Zlength initialized = k_pre + 1) by lia.
  subst j.
  assert (Hp : 1 <= Znth 0 prog 0 <= k_pre).
  { apply PreH9. lia. }
  assert (Hcost0 :
      1 <= Znth (Znth 0 prog 0) (0 :: cold_costs) 0 <= 1000000000).
  { rewrite Znth_cons by lia.
    specialize (PreH10 (Znth 0 prog 0 - 1) ltac:(lia)).
    lia. }
  assert (Hdp_len :
      Zlength (replace_Znth 0 0 initialized) = k_pre + 1).
  { rewrite Zlength_replace_Znth. exact Hinitlen. }
  assert (Hdp0 : Znth 0 (replace_Znth 0 0 initialized) 0 = 0).
  { rewrite Znth_replace_Znth_Same by (rewrite Hinitlen; lia).
    reflexivity. }
  assert (Hdp_range : forall q, 0 <= q <= k_pre ->
      Znth q (replace_Znth 0 0 initialized) 0 = DP_INF \/
      (-1 * 1000000000 <= Znth q (replace_Znth 0 0 initialized) 0 /\
       Znth q (replace_Znth 0 0 initialized) 0 <= 1 * 1000000000)).
  { intros q Hq.
    destruct (Z.eq_dec q 0) as [-> | Hq0].
    - right.
      rewrite Znth_replace_Znth_Same by (rewrite Hinitlen; lia).
      lia.
    - left.
      rewrite Znth_replace_Znth_Diff by (try rewrite Hinitlen; lia).
      apply PreH14. lia. }
  assert (Hstate : NormalizedScheduleState prog cold_costs hot_costs 1
      (replace_Znth 0 0 initialized)
      (Znth (Znth 0 prog 0) (0 :: cold_costs) 0) 0).
  { apply (normalized_schedule_state_initial__initialization
      prog cold_costs hot_costs initialized n_pre k_pre).
    - exact PreH2.
    - exact PreH6.
    - exact PreH4.
    - exact PreH7.
    - exact PreH8.
    - exact PreH9.
    - exact PreH10.
    - exact Hinitlen.
    - intros q Hq.
      apply PreH14.
      rewrite Hinitlen.
      exact Hq. }
  Exists (replace_Znth 0 0 initialized).
  split_pure_spatial.
  - rewrite Hj.
    repeat cancel.
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0).
  set (y := Znth (i - 1) prog 0).
  set (hotc := Znth x (0 :: hot_costs) 0).
  set (coldc := Znth x (0 :: cold_costs) 0).
  assert (Hxy : x = y) by (unfold x, y; exact PreH3).
  assert (Hxbound : 1 <= x <= k_pre).
  { unfold x. apply PreH12. lia. }
  assert (Hidx : 0 <= x < Zlength dp) by lia.
  assert (Hdpdefault : Znth x dp DP_INF = Znth x dp 0).
  { apply Znth_indep. exact Hidx. }
  assert (Hcost : 1 <= Znth (x - 1) hot_costs 0 <=
                  Znth (x - 1) cold_costs 0 /\
                  Znth (x - 1) cold_costs 0 <= 1000000000).
  { apply PreH13. lia. }
  assert (Hhot : hotc = Znth (x - 1) hot_costs 0).
  { unfold hotc. rewrite Znth_cons by lia. reflexivity. }
  assert (Hcold : coldc = Znth (x - 1) cold_costs 0).
  { unfold coldc. rewrite Znth_cons by lia. reflexivity. }
  assert (Hmin : mind <= Znth x dp DP_INF).
  { eapply normalized_schedule_state_min_le__state_transitions;
      [exact PreH25|rewrite <- PreH10; lia|].
    rewrite Hdpdefault. unfold DP_INF. exact PreH2. }
  assert (Hcandcold : Znth x dp 0 + off + hotc <=
      mind + off + Znth (x - 1) cold_costs 0).
  { fold x in PreH1. rewrite !Znth_cons in PreH1 by lia.
    rewrite Hhot. lia. }
  eapply normalized_schedule_state_step__state_transitions with
    (x := x) (y := y) (ca := hotc)
    (cand := Znth x dp 0 + off + hotc)
    (ny := Znth x dp 0) (newdp := dp) (newmind := mind).
  - lia.
  - reflexivity.
  - reflexivity.
  - rewrite PreH10 in PreH16. exact PreH16.
  - rewrite <- PreH10. exact Hxbound.
  - rewrite <- PreH10. lia.
  - intros q Hq. rewrite <- PreH10. apply PreH12. lia.
  - exact (proj2 (proj1 Hcost)).
  - exact PreH25.
  - unfold x, y in PreH3.
    destruct (Z.eq_dec x y); [exact Hhot|contradiction].
  - lia.
  - unfold DP_INF. exact PreH2.
  - exact Hcandcold.
  - intros _. rewrite Hdpdefault, <- Hhot. lia.
  - right. split; [rewrite Hdpdefault; unfold DP_INF; exact PreH2|].
    rewrite Hdpdefault, <- Hhot. lia.
  - right. rewrite <- Hxy, Hdpdefault. split; [lia|reflexivity].
  - right. rewrite Hdpdefault in Hmin. split; [lia|reflexivity].
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  replace (off + Znth (Znth i prog 0) (0 :: hot_costs) 0 -
    Znth (Znth i prog 0) (0 :: hot_costs) 0) with off by lia.
  exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hidx : 0 <= Znth i prog 0 < Zlength dp).
  { specialize (PreH12 i ltac:(lia)). lia. }
  assert (Hdpdefault : Znth (Znth i prog 0) dp DP_INF =
      Znth (Znth i prog 0) dp 0).
  { apply Znth_indep. exact Hidx. }
  pose proof (normalized_schedule_state_min_le__state_transitions
    prog cold_costs hot_costs i dp off mind (Znth i prog 0)
    PreH25 ltac:(rewrite <- PreH10; specialize (PreH12 i ltac:(lia)); lia)
    ltac:(rewrite Hdpdefault; unfold DP_INF; exact PreH2)) as Hmin.
  rewrite Hdpdefault in Hmin.
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite Znth_cons in * by lia.
  destruct PreH13 as [[Hhotpos Hhotcold] Hcoldmax].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  pose proof PreH1 as Hcand.
  set (x := Znth i prog 0).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (x - 1) ltac:(unfold x; lia)).
  assert (Hhotc : Znth x (0 :: hot_costs) 0 = Znth (x - 1) hot_costs 0).
  { rewrite Znth_cons by (unfold x; lia). reflexivity. }
  assert (Hcoldc : Znth x (0 :: cold_costs) 0 = Znth (x - 1) cold_costs 0).
  { rewrite Znth_cons by (unfold x; lia). reflexivity. }
  fold x in Hcand |- *. rewrite Hhotc, Hcoldc in Hcand. rewrite Hhotc.
  destruct PreH13 as [[Hhotpos Hhotcold] Hcoldmax].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_5 : solver_entail_wit_4_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_6 : solver_entail_wit_4_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite Znth_cons in * by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_7 : solver_entail_wit_4_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite Znth_cons in * by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_8 : solver_entail_wit_4_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite Znth_cons in * by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_9 : solver_entail_wit_4_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite Znth_cons in * by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_10 : solver_entail_wit_4_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  apply PreH13. assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_11 : solver_entail_wit_4_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  apply PreH12. assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_8.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_9.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_10.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_11.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0). set (y := Znth (i - 1) prog 0).
  assert (Hx : 1 <= x <= k_pre) by (unfold x; apply PreH12; lia).
  assert (Hy : 1 <= y <= k_pre) by (unfold y; apply PreH12; lia).
  specialize (PreH13 (x - 1) ltac:(lia)).
  fold x in PreH1, H |- *. fold y in H |- *.
  repeat (rewrite Znth_cons in PreH1 by lia).
  repeat (rewrite Znth_cons in H by lia).
  repeat (rewrite Znth_cons by lia).
  pose proof (normalized_unequal_transition_branches__state_transitions
    prog cold_costs hot_costs i dp off mind x y
    ltac:(rewrite <- PreH9; lia) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(rewrite PreH10 in PreH16; exact PreH16)
    ltac:(rewrite <- PreH10; exact Hx) ltac:(rewrite <- PreH10; exact Hy)
    ltac:(intros q Hq; rewrite <- PreH10; apply PreH12; rewrite PreH9; lia)
    ltac:(tauto) PreH25 ltac:(unfold x, y; exact PreH3)
    ltac:(unfold DP_INF; exact PreH2) ltac:(exact PreH1)) as HB.
  apply (proj1 HB). lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0). set (y := Znth (i - 1) prog 0).
  assert (Hx : 1 <= x <= k_pre) by (unfold x; apply PreH12; lia).
  assert (Hy : 1 <= y <= k_pre) by (unfold y; apply PreH12; lia).
  specialize (PreH13 (x - 1) ltac:(lia)).
  fold x in PreH1, H |- *. fold y in H |- *.
  repeat (rewrite Znth_cons in PreH1 by lia).
  repeat (rewrite Znth_cons in H by lia).
  repeat (rewrite Znth_cons by lia).
  pose proof (normalized_unequal_transition_branches__state_transitions
    prog cold_costs hot_costs i dp off mind x y
    ltac:(rewrite <- PreH9; lia) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(rewrite PreH10 in PreH16; exact PreH16)
    ltac:(rewrite <- PreH10; exact Hx) ltac:(rewrite <- PreH10; exact Hy)
    ltac:(intros q Hq; rewrite <- PreH10; apply PreH12; rewrite PreH9; lia)
    ltac:(tauto) PreH25 ltac:(unfold x, y; exact PreH3)
    ltac:(unfold DP_INF; exact PreH2) ltac:(exact PreH1)) as HB.
  replace (Znth x dp 0 + off + Znth (x - 1) hot_costs 0 -
    (off + Znth (x - 1) cold_costs 0)) with
    (Znth x dp 0 + Znth (x - 1) hot_costs 0 -
      Znth (x - 1) cold_costs 0) in H |- * by lia.
  apply (proj1 (proj2 HB)). tauto.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  replace (off + Znth (Znth i prog 0) (0 :: cold_costs) 0 -
    Znth (Znth i prog 0) (0 :: cold_costs) 0) with off by lia.
  exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_4 : solver_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hidx : 0 <= Znth i prog 0 < Zlength dp).
  { specialize (PreH12 i ltac:(lia)). lia. }
  assert (Hdef : Znth (Znth i prog 0) dp DP_INF = Znth (Znth i prog 0) dp 0).
  { apply Znth_indep. exact Hidx. }
  pose proof (normalized_schedule_state_min_le__state_transitions
    prog cold_costs hot_costs i dp off mind (Znth i prog 0) PreH25
    ltac:(rewrite <- PreH10; specialize (PreH12 i ltac:(lia)); lia)
    ltac:(rewrite Hdef; unfold DP_INF; exact PreH2)) as Hmin.
  rewrite Hdef in Hmin.
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  rewrite !Znth_cons in * by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_5 : solver_entail_wit_4_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  pose proof PreH1 as Hcand.
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  repeat (rewrite Znth_cons in Hcand |- * by lia).
  destruct PreH13 as [[? ?] ?]. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_6 : solver_entail_wit_4_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)).
  specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  specialize (PreH24 (Znth i prog 0) ltac:(lia)).
  repeat (rewrite Znth_cons in * by lia).
  destruct PreH13 as [[? ?] ?]. destruct PreH24; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_7 : solver_entail_wit_4_2_split_goal_7.
Proof. LLM_pre_process ltac:(lia || nia || int_auto || auto). Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_8 : solver_entail_wit_4_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)). specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  repeat (rewrite Znth_cons in * by lia). lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_9 : solver_entail_wit_4_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)). specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  repeat (rewrite Znth_cons in * by lia). lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_10 : solver_entail_wit_4_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)). specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  repeat (rewrite Znth_cons in * by lia). lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_11 : solver_entail_wit_4_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  specialize (PreH12 i ltac:(lia)). specialize (PreH13 (Znth i prog 0 - 1) ltac:(lia)).
  repeat (rewrite Znth_cons in * by lia). lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_12 : solver_entail_wit_4_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  apply PreH13. assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_13 : solver_entail_wit_4_2_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  apply PreH12. assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_8.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_9.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_10.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_11.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_12.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_13.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0). set (y := Znth (i - 1) prog 0).
  pose proof PreH13 as Hallcost.
  assert (Hx : 1 <= x <= k_pre) by (unfold x; apply PreH12; lia).
  assert (Hy : 1 <= y <= k_pre) by (unfold y; apply PreH12; lia).
  specialize (PreH13 (x - 1) ltac:(lia)).
  assert (Hhotc : Znth x (0 :: hot_costs) 0 = Znth (x - 1) hot_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcoldc : Znth x (0 :: cold_costs) 0 = Znth (x - 1) cold_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcandidate : mind + off + Znth (x - 1) cold_costs 0 <=
      Znth x dp_2 0 + off + Znth (x - 1) hot_costs 0).
  { fold x in PreH1. rewrite Hhotc, Hcoldc in PreH1. lia. }
  pose proof (normalized_baseline_transition_branches__state_transitions
    prog cold_costs hot_costs i dp_2 off mind x y
    (Znth (x - 1) hot_costs 0)
    ltac:(rewrite <- PreH9; lia) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(rewrite PreH10 in PreH16; exact PreH16)
    ltac:(rewrite <- PreH10; exact Hx) ltac:(rewrite <- PreH10; exact Hy)
    ltac:(intros q Hq; rewrite <- PreH10; apply PreH12; rewrite PreH9; lia)
    ltac:(tauto) PreH25
    ltac:(unfold x, y in PreH3;
      destruct (Z.eq_dec x y); [reflexivity|contradiction])
    ltac:(tauto) ltac:(tauto) PreH21 Hcandidate) as HB.
  cbn in HB.
  Left. Exists dp_2. split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; rewrite Hhotc || rewrite Hcoldc; lia);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia; lia);
      try (dump_pre_spatial; replace
        (off + Znth x (0 :: hot_costs) 0 - Znth x (0 :: hot_costs) 0)
        with off by lia; exact PreH25);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 HB); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 (proj2 HB)); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj2 (proj2 HB)); tauto).
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) hot_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) hot_costs 0) in HH |- * by lia;
        apply (proj1 (proj2 HB)); destruct HH; split; lia);
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) hot_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) hot_costs 0) in HH |- * by lia;
        apply (proj2 (proj2 HB)); exact HH).
  all: dump_pre_spatial.
  all: rewrite Hhotc, Hcoldc.
  all: intros HH.
  all: replace (mind + off + Znth (x - 1) cold_costs 0 -
      (off + Znth (x - 1) hot_costs 0)) with
      (mind + Znth (x - 1) cold_costs 0 -
        Znth (x - 1) hot_costs 0) in HH |- * by lia.
  all: apply (proj2 (proj2 HB)); lia.
Qed.

Lemma proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0). set (y := Znth (i - 1) prog 0).
  pose proof PreH13 as Hallcost.
  assert (Hx : 1 <= x <= k_pre) by (unfold x; apply PreH12; lia).
  assert (Hy : 1 <= y <= k_pre) by (unfold y; apply PreH12; lia).
  specialize (PreH13 (x - 1) ltac:(lia)).
  assert (Hhotc : Znth x (0 :: hot_costs) 0 = Znth (x - 1) hot_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcoldc : Znth x (0 :: cold_costs) 0 = Znth (x - 1) cold_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcandidate : mind + off + Znth (x - 1) cold_costs 0 <=
      Znth x dp_2 0 + off + Znth (x - 1) hot_costs 0).
  { fold x in PreH1. rewrite Hhotc, Hcoldc in PreH1. lia. }
  pose proof (normalized_baseline_transition_branches__state_transitions
    prog cold_costs hot_costs i dp_2 off mind x y
    (Znth (x - 1) cold_costs 0)
    ltac:(rewrite <- PreH9; lia) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(rewrite PreH10 in PreH16; exact PreH16)
    ltac:(rewrite <- PreH10; exact Hx) ltac:(rewrite <- PreH10; exact Hy)
    ltac:(intros q Hq; rewrite <- PreH10; apply PreH12; rewrite PreH9; lia)
    ltac:(tauto) PreH25
    ltac:(unfold x, y in PreH3;
      destruct (Z.eq_dec x y); [contradiction|reflexivity])
    ltac:(lia) ltac:(tauto) PreH21 Hcandidate) as HB.
  cbn in HB.
  Left. Exists dp_2. split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; rewrite Hhotc || rewrite Hcoldc; lia);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia; lia);
      try (dump_pre_spatial; replace
        (off + Znth x (0 :: cold_costs) 0 - Znth x (0 :: cold_costs) 0)
        with off by lia; exact PreH25);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 HB); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 (proj2 HB)); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj2 (proj2 HB)); tauto).
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) cold_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) cold_costs 0) in HH |- * by lia;
        apply (proj1 (proj2 HB)); destruct HH; split; lia);
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) cold_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) cold_costs 0) in HH |- * by lia;
        apply (proj2 (proj2 HB)); exact HH).
  all: dump_pre_spatial.
  all: try rewrite Hhotc; try rewrite Hcoldc.
  all: intros HH.
  all: replace (mind + off + Znth (x - 1) cold_costs 0 -
      (off + Znth (x - 1) cold_costs 0)) with
      (mind + Znth (x - 1) cold_costs 0 -
        Znth (x - 1) cold_costs 0) in HH |- * by lia.
  all: first
    [ apply (proj1 (proj2 HB)); lia
    | apply (proj2 (proj2 HB)); lia ].
Qed.

Lemma proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0). set (y := Znth (i - 1) prog 0).
  pose proof PreH12 as Hallcost.
  assert (Hx : 1 <= x <= k_pre) by (unfold x; apply PreH11; lia).
  assert (Hy : 1 <= y <= k_pre) by (unfold y; apply PreH11; lia).
  specialize (PreH12 (x - 1) ltac:(lia)).
  assert (Hhotc : Znth x (0 :: hot_costs) 0 = Znth (x - 1) hot_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcoldc : Znth x (0 :: cold_costs) 0 = Znth (x - 1) cold_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcandidate : mind + off + Znth (x - 1) cold_costs 0 <=
      Znth x dp_2 0 + off + Znth (x - 1) hot_costs 0).
  { fold x in PreH1. lia. }
  pose proof (normalized_baseline_transition_branches__state_transitions
    prog cold_costs hot_costs i dp_2 off mind x y
    (Znth (x - 1) hot_costs 0)
    ltac:(rewrite <- PreH8; lia) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(rewrite PreH9 in PreH15; exact PreH15)
    ltac:(rewrite <- PreH9; exact Hx) ltac:(rewrite <- PreH9; exact Hy)
    ltac:(intros q Hq; rewrite <- PreH9; apply PreH11; rewrite PreH8; lia)
    ltac:(tauto) PreH24
    ltac:(unfold x, y in PreH2;
      destruct (Z.eq_dec x y); [reflexivity|contradiction])
    ltac:(tauto) ltac:(tauto) PreH20 Hcandidate) as HB.
  cbn in HB.
  Left. Exists dp_2. split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; rewrite Hhotc || rewrite Hcoldc; lia);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia; lia);
      try (dump_pre_spatial; replace
        (off + Znth x (0 :: hot_costs) 0 - Znth x (0 :: hot_costs) 0)
        with off by lia; exact PreH24);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 HB); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 (proj2 HB)); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj2 (proj2 HB)); tauto).
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) hot_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) hot_costs 0) in HH |- * by lia;
        apply (proj1 (proj2 HB)); destruct HH; split; lia);
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) hot_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) hot_costs 0) in HH |- * by lia;
        apply (proj2 (proj2 HB)); exact HH).
  all: dump_pre_spatial.
  all: rewrite Hhotc, Hcoldc.
  all: intros HH.
  all: replace (mind + off + Znth (x - 1) cold_costs 0 -
      (off + Znth (x - 1) hot_costs 0)) with
      (mind + Znth (x - 1) cold_costs 0 -
        Znth (x - 1) hot_costs 0) in HH |- * by lia.
  all: apply (proj2 (proj2 HB)); lia.
Qed.

Lemma proof_of_solver_entail_wit_4_6 : solver_entail_wit_4_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  set (x := Znth i prog 0). set (y := Znth (i - 1) prog 0).
  pose proof PreH12 as Hallcost.
  assert (Hx : 1 <= x <= k_pre) by (unfold x; apply PreH11; lia).
  assert (Hy : 1 <= y <= k_pre) by (unfold y; apply PreH11; lia).
  specialize (PreH12 (x - 1) ltac:(lia)).
  assert (Hhotc : Znth x (0 :: hot_costs) 0 = Znth (x - 1) hot_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcoldc : Znth x (0 :: cold_costs) 0 = Znth (x - 1) cold_costs 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hcandidate : mind + off + Znth (x - 1) cold_costs 0 <=
      Znth x dp_2 0 + off + Znth (x - 1) hot_costs 0).
  { fold x in PreH1. lia. }
  pose proof (normalized_baseline_transition_branches__state_transitions
    prog cold_costs hot_costs i dp_2 off mind x y
    (Znth (x - 1) cold_costs 0)
    ltac:(rewrite <- PreH8; lia) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(rewrite PreH9 in PreH15; exact PreH15)
    ltac:(rewrite <- PreH9; exact Hx) ltac:(rewrite <- PreH9; exact Hy)
    ltac:(intros q Hq; rewrite <- PreH9; apply PreH11; rewrite PreH8; lia)
    ltac:(tauto) PreH24
    ltac:(unfold x, y in PreH2;
      destruct (Z.eq_dec x y); [contradiction|reflexivity])
    ltac:(lia) ltac:(tauto) PreH20 Hcandidate) as HB.
  cbn in HB.
  Left. Exists dp_2. split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; rewrite Hhotc || rewrite Hcoldc; lia);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia; lia);
      try (dump_pre_spatial; replace
        (off + Znth x (0 :: cold_costs) 0 - Znth x (0 :: cold_costs) 0)
        with off by lia; exact PreH24);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 HB); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj1 (proj2 HB)); tauto);
      try (dump_pre_spatial; repeat rewrite Znth_cons by lia;
        apply (proj2 (proj2 HB)); tauto).
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) cold_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) cold_costs 0) in HH |- * by lia;
        apply (proj1 (proj2 HB)); destruct HH; split; lia);
      try (dump_pre_spatial; rewrite Hhotc, Hcoldc; intros HH;
        replace (mind + off + Znth (x - 1) cold_costs 0 -
          (off + Znth (x - 1) cold_costs 0)) with
          (mind + Znth (x - 1) cold_costs 0 -
            Znth (x - 1) cold_costs 0) in HH |- * by lia;
        apply (proj2 (proj2 HB)); exact HH).
  all: dump_pre_spatial.
  all: try rewrite Hhotc; try rewrite Hcoldc.
  all: intros HH.
  all: replace (mind + off + Znth (x - 1) cold_costs 0 -
      (off + Znth (x - 1) cold_costs 0)) with
      (mind + Znth (x - 1) cold_costs 0 -
        Znth (x - 1) cold_costs 0) in HH |- * by lia.
  all: first
    [ apply (proj1 (proj2 HB)); lia
    | apply (proj2 (proj2 HB)); lia ].
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply replace_Znth_dp_bounds__state_write_update; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Znth_zero_replace_positive__state_write_update.
  - rewrite PreH24. lia.
  - exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth__state_write_update.
  exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_4 : solver_entail_wit_5_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_5 : solver_entail_wit_5_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply replace_Znth_dp_bounds__state_write_update; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Znth_zero_replace_positive__state_write_update.
  - rewrite PreH24. lia.
  - exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_3 : solver_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth__state_write_update.
  exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_4 : solver_entail_wit_5_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_5 : solver_entail_wit_5_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply replace_Znth_dp_bounds__state_write_update; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_2 : solver_entail_wit_5_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Znth_zero_replace_positive__state_write_update.
  - rewrite PreH24. lia.
  - exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_3 : solver_entail_wit_5_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth__state_write_update.
  exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_4 : solver_entail_wit_5_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_5 : solver_entail_wit_5_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_1 : solver_entail_wit_5_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply replace_Znth_dp_bounds__state_write_update; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_2 : solver_entail_wit_5_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Znth_zero_replace_positive__state_write_update.
  - rewrite PreH24. lia.
  - exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_3 : solver_entail_wit_5_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth__state_write_update.
  exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_4 : solver_entail_wit_5_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_5 : solver_entail_wit_5_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_1 : solver_entail_wit_5_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply replace_Znth_dp_bounds__state_write_update; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_2 : solver_entail_wit_5_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Znth_zero_replace_positive__state_write_update.
  - rewrite PreH24. lia.
  - exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_3 : solver_entail_wit_5_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth__state_write_update.
  exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_4 : solver_entail_wit_5_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_5 : solver_entail_wit_5_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_1 : solver_entail_wit_5_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH33 q_3 H).
  destruct PreH33 as [Hinf | [Hlo Hhi]].
  - left. exact Hinf.
  - right. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_2 : solver_entail_wit_5_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH10 q_2 H).
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_3 : solver_entail_wit_5_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 q H).
Qed.

Lemma proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_7_split_goal_1 : solver_entail_wit_5_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH33 q_3 H).
  destruct PreH33 as [Hinf | [Hlo Hhi]].
  - left. exact Hinf.
  - right. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_7_split_goal_2 : solver_entail_wit_5_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH10 q_2 H).
Qed.

Lemma proof_of_solver_entail_wit_5_7_split_goal_3 : solver_entail_wit_5_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 q H).
Qed.

Lemma proof_of_solver_entail_wit_5_7 : solver_entail_wit_5_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_7_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_8_split_goal_1 : solver_entail_wit_5_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH33 q_3 H).
  destruct PreH33 as [Hinf | [Hlo Hhi]].
  - left. exact Hinf.
  - right. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_8_split_goal_2 : solver_entail_wit_5_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH10 q_2 H).
Qed.

Lemma proof_of_solver_entail_wit_5_8_split_goal_3 : solver_entail_wit_5_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 q H).
Qed.

Lemma proof_of_solver_entail_wit_5_8 : solver_entail_wit_5_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_8_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_9_split_goal_1 : solver_entail_wit_5_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH33 q_3 H).
  destruct PreH33 as [Hinf | [Hlo Hhi]].
  - left. exact Hinf.
  - right. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_9_split_goal_2 : solver_entail_wit_5_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH10 q_2 H).
Qed.

Lemma proof_of_solver_entail_wit_5_9_split_goal_3 : solver_entail_wit_5_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 q H).
Qed.

Lemma proof_of_solver_entail_wit_5_9 : solver_entail_wit_5_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_9_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (i = Zlength prog) by lia.
  subst i.
  replace (mind + off) with (off + mind) by lia.
  apply (normalized_schedule_state_full_spec prog cold_costs hot_costs dp off mind).
  exact PreH22.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (Int64Array.full_to_full_shape d_pre (k_pre + 1) dp).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
