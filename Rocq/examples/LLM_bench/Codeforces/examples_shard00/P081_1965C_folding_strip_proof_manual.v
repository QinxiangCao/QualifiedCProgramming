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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P081_1965C_folding_strip_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P081_1965C_folding_strip_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P081_1965C_folding_strip_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply fold_prefix_alternating_empty__initialization_and_final_result.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
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
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  assert (Hchar : Znth i text 0 = 48).
  { destruct (PreH8 i ltac:(lia)); congruence. }
  rewrite Hchar. rewrite Z.min_l by lia.
  split; intro Hbad; [lia|].
  apply (proj2 (Z_land_one_even__alternating_transitions cur)) in Hbad.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj1 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
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
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  rewrite PreH3. rewrite Z.min_l by lia.
  split; intro H; [|reflexivity].
  apply (proj1 (Z_land_one_even__alternating_transitions cur)). exact PreH4.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj1 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  rewrite PreH3. rewrite Z.min_r by lia.
  assert (Hodd : Z.even cur = false).
  { destruct (Z.even cur) eqn:He; [|reflexivity].
    exfalso. apply PreH4.
    apply (proj2 (Z_land_one_even__alternating_transitions cur)). exact He. }
  rewrite Z.even_sub, Hodd.
  change (49 = 49 <-> true = true). split; intro; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj2 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  assert (Hchar : Znth i text 0 = 48).
  { destruct (PreH8 i ltac:(lia)); congruence. }
  assert (Heven : Z.even cur = true).
  { apply (proj1 (Z_land_one_even__alternating_transitions cur)). exact PreH4. }
  rewrite Hchar. rewrite Z.min_r by lia.
  rewrite Z.even_sub, Heven.
  change (48 = 49 <-> false = true). split; intro Hbad; discriminate.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_2 : solver_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj2 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_5_split_goal_1 : solver_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  assert (Hchar : Znth i text 0 = 48).
  { destruct (PreH8 i ltac:(lia)); congruence. }
  rewrite Hchar. rewrite Z.min_l by lia.
  split; intro Hbad; [lia|].
  apply (proj2 (Z_land_one_even__alternating_transitions cur)) in Hbad.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_5_split_goal_2 : solver_entail_wit_2_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj1 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_6_split_goal_1 : solver_entail_wit_2_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  rewrite PreH3. rewrite Z.min_l by lia.
  split; intro H; [|reflexivity].
  apply (proj1 (Z_land_one_even__alternating_transitions cur)). exact PreH4.
Qed.

Lemma proof_of_solver_entail_wit_2_6_split_goal_2 : solver_entail_wit_2_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj1 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_6 : solver_entail_wit_2_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_7_split_goal_1 : solver_entail_wit_2_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  rewrite PreH3. rewrite Z.min_r by lia.
  assert (Hodd : Z.even cur = false).
  { destruct (Z.even cur) eqn:He; [|reflexivity].
    exfalso. apply PreH4.
    apply (proj2 (Z_land_one_even__alternating_transitions cur)). exact He. }
  rewrite Z.even_sub, Hodd.
  change (49 = 49 <-> true = true). split; intro; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_7_split_goal_2 : solver_entail_wit_2_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj2 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_7 : solver_entail_wit_2_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_8_split_goal_1 : solver_entail_wit_2_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply fold_prefix_alternating_step__alternating_transitions;
    try exact PreH17; try lia; try (left; lia); try (right; lia).
  rewrite app_Znth1 in PreH3 by lia.
  assert (Hchar : Znth i text 0 = 48).
  { destruct (PreH8 i ltac:(lia)); congruence. }
  assert (Heven : Z.even cur = true).
  { apply (proj1 (Z_land_one_even__alternating_transitions cur)). exact PreH4. }
  rewrite Hchar. rewrite Z.min_r by lia.
  rewrite Z.even_sub, Heven.
  change (48 = 49 <-> false = true). split; intro Hbad; discriminate.
Qed.

Lemma proof_of_solver_entail_wit_2_8_split_goal_2 : solver_entail_wit_2_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj2 (Z_land_one_step_parity__alternating_transitions cur i PreH16)).
Qed.

Lemma proof_of_solver_entail_wit_2_8 : solver_entail_wit_2_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_8_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (fold_prefix_alternating_to_spec__initialization_and_final_result
    text i cur mn mx); eauto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
