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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P052_1168A_increasing_by_modulo_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P052_1168A_increasing_by_modulo_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P052_1168A_increasing_by_modulo_lib.
Local Open Scope sac.

Lemma proof_of_feasible_entail_wit_1_split_goal_1 : feasible_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GreedyPrefixState.
  repeat split; try lia.
Qed.

Lemma proof_of_feasible_entail_wit_1_split_goal_2 : feasible_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8; assumption.
Qed.

Lemma proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_2_1_split_goal_1 : feasible_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH14 i ltac:(lia)) as Hvalue.
  eapply greedy_prefix_extend__feasible_prefix with (inc := 0); try eassumption; try lia.
  - rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
  - intros endpoint competing_inc Hinc Hendpoint Hlast.
    subst endpoint.
    rewrite Z.mod_small by lia.
    lia.
Qed.

Lemma proof_of_feasible_entail_wit_2_1 : feasible_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_2_2_split_goal_1 : feasible_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH14 i ltac:(lia)) as Hvalue.
  pose proof PreH15 as Hstate.
  unfold GreedyPrefixState in Hstate.
  destruct Hstate as (_ & Hlastbound & _).
  eapply greedy_prefix_extend__feasible_prefix with (inc := last - Znth i values 0);
    try eassumption; try lia.
  - replace (Znth i values 0 + (last - Znth i values 0)) with last by lia.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma proof_of_feasible_entail_wit_2_2 : feasible_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_2_3_split_goal_1 : feasible_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH14 i ltac:(lia)) as Hvalue.
  eapply greedy_prefix_extend__feasible_prefix with (inc := 0); try eassumption; try lia.
  - rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
  - intros endpoint competing_inc Hinc Hendpoint Hlast.
    subst endpoint.
    destruct (Z_lt_ge_dec (Znth i values 0 + competing_inc) mv) as [Hsmall | Hwrap].
    + rewrite Z.mod_small by lia. lia.
    + rewrite mod_once__feasible_prefix in Hlast by lia.
      rewrite Z.rem_mod_nonneg in PreH1 by lia.
      rewrite mod_once__feasible_prefix in PreH1 by lia.
      lia.
Qed.

Lemma proof_of_feasible_entail_wit_2_3 : feasible_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_2_4_split_goal_1 : feasible_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH13 i ltac:(lia)) as Hvalue.
  pose proof PreH14 as Hstate.
  unfold GreedyPrefixState in Hstate.
  destruct Hstate as (_ & Hlastbound & _).
  eapply greedy_prefix_extend__feasible_prefix with (inc := last - Znth i values 0);
    try eassumption; try lia.
  - replace (Znth i values 0 + (last - Znth i values 0)) with last by lia.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma proof_of_feasible_entail_wit_2_4 : feasible_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_4_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_2_5_split_goal_1 : feasible_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH14 i ltac:(lia)) as Hvalue.
  pose proof PreH15 as Hstate.
  unfold GreedyPrefixState in Hstate.
  destruct Hstate as (_ & Hlastbound & _).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  assert (Hobserved : (Znth i values 0 + x_pre) mod mv =
      Znth i values 0 + x_pre - mv).
  { apply mod_once__feasible_prefix; lia. }
  eapply greedy_prefix_extend__feasible_prefix
    with (inc := mv - Znth i values 0 + last); try eassumption; try lia.
  - replace (Znth i values 0 + (mv - Znth i values 0 + last))
      with (last + mv) by lia.
    rewrite Z.add_mod by lia.
    rewrite Z.mod_same by lia.
    rewrite Z.add_0_r.
    rewrite Z.mod_mod by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
Qed.

Lemma proof_of_feasible_entail_wit_2_5 : feasible_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_5_split_goal_1.
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_1 : feasible_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split.
  - intros _.
    apply greedy_prefix_complete_feasible__feasible_results with
      (i := i) (last := last); auto; lia.
  - lia.
Qed.

Lemma proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_feasible_return_wit_2_split_goal_1 : feasible_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split.
  - lia.
  - intros Hfeasible.
    pose proof (PreH13 i ltac:(lia)) as [Hcurrent_nonneg _].
    exfalso.
    apply (greedy_prefix_failure_infeasible__feasible_results
      mv values x_pre i last); auto; lia.
Qed.

Lemma proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_9_split_goal_1 : solver_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_9_split_goal_2 : solver_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  assert (Hfeasible : Feasible modulus values (modulus - 1)).
  {
    apply feasible_at_modulus_minus_one__solver_boundary.
    - exact PreH1.
    - exact PreH5.
  }
  assert (Hnonempty : values <> nil).
  {
    intro Hnil.
    subst values.
    rewrite Zlength_nil in PreH3.
    lia.
  }
  destruct (bounded_minimum_feasible_round__solver_boundary
    modulus values (modulus - 1) Hnonempty Hfeasible)
    as [out [Hspec [Hout_nonneg Hout_upper]]].
  unfold SearchState.
  split; [exact Hfeasible|].
  split; [lia|].
  exists out.
  split; [exact Hspec|].
  left.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
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
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  eapply search_state_feasible_mid_step__solver_transitions.
  - exact PreH19.
  - apply (proj1 PreH3); exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_3 : solver_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_4 : solver_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_5 : solver_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_6 : solver_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  eapply search_state_infeasible_mid_step__solver_transitions.
  - exact PreH19.
  - intro Hmid_feasible.
    apply (proj2 PreH3) in Hmid_feasible.
    contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_4 : solver_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (midpoint_bounds__solver_transitions lo hi PreH11 PreH4).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst mm_pre.
  apply (search_state_closed_interval__solver_boundary
    modulus values lo hi ans PreH1 PreH16).
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_2 : solver_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_3 : solver_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros j Hj.
  apply PreH27.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_4 : solver_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_4.
Qed.
