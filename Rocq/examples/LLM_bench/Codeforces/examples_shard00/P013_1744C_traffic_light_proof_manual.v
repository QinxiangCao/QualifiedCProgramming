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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P013_1744C_traffic_light_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P013_1744C_traffic_light_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_red_split_goal_1 : solver_entail_wit_1_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH2.
  apply traffic_scan_state_initial__initialization.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_red_split_goal_2 : solver_entail_wit_1_red_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_red : solver_entail_wit_1_red.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_red_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_red_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_yellow_split_goal_1 : solver_entail_wit_2_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH2.
  apply traffic_scan_state_initial__initialization.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_yellow_split_goal_2 : solver_entail_wit_2_yellow_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_yellow : solver_entail_wit_2_yellow.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_yellow_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_yellow_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_red_split_goal_1 : solver_entail_wit_3_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound i n ltac:(lia)) as Hmod.
  exact (proj2 Hmod).
Qed.

Lemma proof_of_solver_entail_wit_3_red_split_goal_2 : solver_entail_wit_3_red_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound i n ltac:(lia)) as Hmod.
  exact (proj1 Hmod).
Qed.

Lemma proof_of_solver_entail_wit_3_red : solver_entail_wit_3_red.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_red_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_red_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_yellow_split_goal_1 : solver_entail_wit_4_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound i n ltac:(lia)) as Hmod.
  exact (proj2 Hmod).
Qed.

Lemma proof_of_solver_entail_wit_4_yellow_split_goal_2 : solver_entail_wit_4_yellow_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound i n ltac:(lia)) as Hmod.
  exact (proj1 Hmod).
Qed.

Lemma proof_of_solver_entail_wit_4_yellow : solver_entail_wit_4_yellow.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_yellow_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_yellow_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_1_red_split_goal_1 : solver_entail_wit_5_1_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : DoubledTrafficChar lights i = 114).
  {
    unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia.
    rewrite <- (app_Znth1 0 lights (0 :: nil) i) by lia.
    assert (Hi_rem : Z.rem i n = i) by (apply Z.rem_small; lia).
    rewrite Hi_rem in PreH2.
    rewrite PreH15 in PreH2.
    exact PreH2.
  }
  pose proof
    (traffic_scan_step_current_raise__current_max_update
       114 lights i ans next_green
       ltac:(rewrite <- PreH15; exact PreH17)
       ltac:(lia) ltac:(lia) Hchar
       ltac:(rewrite <- PreH15; exact PreH24)
       ltac:(lia) ltac:(lia)) as Hstep.
  exact (proj1 Hstep).
Qed.

Lemma proof_of_solver_entail_wit_5_1_red_split_goal_2 : solver_entail_wit_5_1_red_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : DoubledTrafficChar lights i = 114).
  {
    unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia.
    rewrite <- (app_Znth1 0 lights (0 :: nil) i) by lia.
    assert (Hi_rem : Z.rem i n = i) by (apply Z.rem_small; lia).
    rewrite Hi_rem in PreH2.
    rewrite PreH15 in PreH2.
    exact PreH2.
  }
  pose proof
    (traffic_scan_step_current_raise__current_max_update
       114 lights i ans next_green
       ltac:(rewrite <- PreH15; exact PreH17)
       ltac:(lia) ltac:(lia) Hchar
       ltac:(rewrite <- PreH15; exact PreH24)
       ltac:(lia) ltac:(lia)) as Hstep.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_red : solver_entail_wit_5_1_red.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_red_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_red_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_2_red_split_goal_1 : solver_entail_wit_5_2_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c. subst n.
  rewrite app_Znth1 in PreH1 by lia.
  rewrite app_Znth1 in PreH3 by lia.
  rewrite Z.rem_small in PreH1 by lia.
  rewrite Z.rem_small in PreH3 by lia.
  apply traffic_scan_step_noncurrent_nongreen__stable_transition.
  - lia.
  - exact PreH1.
  - unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia. exact PreH3.
  - exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_5_2_red : solver_entail_wit_5_2_red.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_2_red_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_3_red_split_goal_1 : solver_entail_wit_5_3_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c.
  subst n.
  rewrite app_Znth1 in PreH1 by lia.
  rewrite app_Znth1 in PreH3 by lia.
  rewrite Z.rem_mod_nonneg in PreH1, PreH3 by lia.
  rewrite Z.mod_small in PreH1 by lia.
  eapply traffic_scan_step_green_noncurrent__green_transition.
  - lia.
  - unfold DoubledTrafficChar.
    exact PreH3.
  - exact PreH1.
  - exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_5_3_red : solver_entail_wit_5_3_red.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_3_red_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_4_red_split_goal_1 : solver_entail_wit_5_4_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c.
  subst n.
  rewrite app_Znth1 in PreH2 by lia.
  rewrite Z.rem_mod_nonneg in PreH2 by lia.
  eapply traffic_scan_step_green_outside_original__green_transition.
  - lia.
  - unfold DoubledTrafficChar.
    exact PreH2.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_5_4_red : solver_entail_wit_5_4_red.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_4_red_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_5_red_split_goal_1 : solver_entail_wit_5_5_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c. subst n.
  rewrite app_Znth1 in PreH2 by lia.
  apply traffic_scan_step_nongreen_outside_original__stable_transition.
  - lia.
  - unfold DoubledTrafficChar.
    rewrite <- Z.rem_mod_nonneg by lia. exact PreH2.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_5_5_red : solver_entail_wit_5_5_red.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_5_red_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_6_red_split_goal_1 : solver_entail_wit_5_6_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c. subst n.
  rewrite app_Znth1 in PreH4 by lia.
  rewrite Z.rem_small in PreH4 by lia.
  rewrite PreH15 in PreH24.
  apply traffic_scan_step_current_keep__stable_transition.
  - lia.
  - unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia. exact PreH4.
  - exact PreH1.
  - exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_6_red : solver_entail_wit_5_6_red.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_6_red_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_1_yellow_split_goal_1 : solver_entail_wit_6_1_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : DoubledTrafficChar lights i = 121).
  {
    unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia.
    rewrite <- (app_Znth1 0 lights (0 :: nil) i) by lia.
    assert (Hi_rem : Z.rem i n = i) by (apply Z.rem_small; lia).
    rewrite Hi_rem in PreH2.
    rewrite PreH15 in PreH2.
    exact PreH2.
  }
  pose proof
    (traffic_scan_step_current_raise__current_max_update
       121 lights i ans next_green
       ltac:(rewrite <- PreH15; exact PreH17)
       ltac:(lia) ltac:(lia) Hchar
       ltac:(rewrite <- PreH15; exact PreH24)
       ltac:(lia) ltac:(lia)) as Hstep.
  exact (proj1 Hstep).
Qed.

Lemma proof_of_solver_entail_wit_6_1_yellow_split_goal_2 : solver_entail_wit_6_1_yellow_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : DoubledTrafficChar lights i = 121).
  {
    unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia.
    rewrite <- (app_Znth1 0 lights (0 :: nil) i) by lia.
    assert (Hi_rem : Z.rem i n = i) by (apply Z.rem_small; lia).
    rewrite Hi_rem in PreH2.
    rewrite PreH15 in PreH2.
    exact PreH2.
  }
  pose proof
    (traffic_scan_step_current_raise__current_max_update
       121 lights i ans next_green
       ltac:(rewrite <- PreH15; exact PreH17)
       ltac:(lia) ltac:(lia) Hchar
       ltac:(rewrite <- PreH15; exact PreH24)
       ltac:(lia) ltac:(lia)) as Hstep.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_1_yellow : solver_entail_wit_6_1_yellow.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_1_yellow_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_1_yellow_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_2_yellow_split_goal_1 : solver_entail_wit_6_2_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c. subst n.
  rewrite app_Znth1 in PreH1 by lia.
  rewrite app_Znth1 in PreH3 by lia.
  rewrite Z.rem_small in PreH1 by lia.
  rewrite Z.rem_small in PreH3 by lia.
  apply traffic_scan_step_noncurrent_nongreen__stable_transition.
  - lia.
  - exact PreH1.
  - unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia. exact PreH3.
  - exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_6_2_yellow : solver_entail_wit_6_2_yellow.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_2_yellow_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_3_yellow_split_goal_1 : solver_entail_wit_6_3_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c.
  subst n.
  rewrite app_Znth1 in PreH1 by lia.
  rewrite app_Znth1 in PreH3 by lia.
  rewrite Z.rem_mod_nonneg in PreH1, PreH3 by lia.
  rewrite Z.mod_small in PreH1 by lia.
  eapply traffic_scan_step_green_noncurrent__green_transition.
  - lia.
  - unfold DoubledTrafficChar.
    exact PreH3.
  - exact PreH1.
  - exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_6_3_yellow : solver_entail_wit_6_3_yellow.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_3_yellow_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_4_yellow_split_goal_1 : solver_entail_wit_6_4_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c.
  subst n.
  rewrite app_Znth1 in PreH2 by lia.
  rewrite Z.rem_mod_nonneg in PreH2 by lia.
  eapply traffic_scan_step_green_outside_original__green_transition.
  - lia.
  - unfold DoubledTrafficChar.
    exact PreH2.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_6_4_yellow : solver_entail_wit_6_4_yellow.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_4_yellow_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_5_yellow_split_goal_1 : solver_entail_wit_6_5_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c. subst n.
  rewrite app_Znth1 in PreH2 by lia.
  apply traffic_scan_step_nongreen_outside_original__stable_transition.
  - lia.
  - unfold DoubledTrafficChar.
    rewrite <- Z.rem_mod_nonneg by lia. exact PreH2.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_6_5_yellow : solver_entail_wit_6_5_yellow.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_5_yellow_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_6_yellow_split_goal_1 : solver_entail_wit_6_6_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c. subst n.
  rewrite app_Znth1 in PreH4 by lia.
  rewrite Z.rem_small in PreH4 by lia.
  rewrite PreH15 in PreH24.
  apply traffic_scan_step_current_keep__stable_transition.
  - lia.
  - unfold DoubledTrafficChar.
    rewrite Z.mod_small by lia. exact PreH4.
  - exact PreH1.
  - exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_6_6_yellow : solver_entail_wit_6_6_yellow.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_6_yellow_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_red_split_goal_1 : solver_return_wit_1_red_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c.
  eapply traffic_scan_exit_implies_spec__final_results
    with (i := i) (next := next_green).
  - lia.
  - exact PreH7.
  - exact PreH14.
Qed.

Lemma proof_of_solver_return_wit_1_red : solver_return_wit_1_red.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_red_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_yellow_split_goal_1 : solver_return_wit_2_yellow_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c.
  eapply traffic_scan_exit_implies_spec__final_results
    with (i := i) (next := next_green).
  - lia.
  - exact PreH7.
  - exact PreH14.
Qed.

Lemma proof_of_solver_return_wit_2_yellow : solver_return_wit_2_yellow.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_yellow_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_green_split_goal_1 : solver_return_wit_3_green_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst c_pre.
  apply green_current_spec_zero__final_results.
  assumption.
Qed.

Lemma proof_of_solver_return_wit_3_green : solver_return_wit_3_green.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_green_split_goal_1.
Qed.
