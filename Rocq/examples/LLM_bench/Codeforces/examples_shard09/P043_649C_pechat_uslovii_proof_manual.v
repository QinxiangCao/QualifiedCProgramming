From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P043_649C_pechat_uslovii_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P043_649C_pechat_uslovii_proof_auto.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P043_649C_pechat_uslovii_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_int64_range (&( "x" )) x).
  Intros_p Hxrange.
  change (-9223372036854775808 <= x <= 9223372036854775807) in Hxrange.
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hq : 0 <= Znth i sorted_pages 0 / 2).
  { apply Z.div_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in PreH1 by lia.
  pose proof (Z.div_mod (Znth i sorted_pages 0) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Znth i sorted_pages 0) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_8_split_goal_1 : solver_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in PreH1 by lia.
  pose proof (Z.div_mod (Znth i sorted_pages 0) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Znth i sorted_pages 0) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_8_split_goal_2 : solver_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in * by lia.
  pose proof (Z.div_mod (Znth i sorted_pages 0) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Znth i sorted_pages 0) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in * by lia.
  pose proof (Z.div_mod (Znth i sorted_pages 0) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Znth i sorted_pages 0) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in * by lia.
  pose proof (Z.div_mod (Znth i sorted_pages 0) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Znth i sorted_pages 0) 2 ltac:(lia)) as Hmod.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 i ltac:(lia)).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hq : 0 <= Znth i sorted_pages 0 / 2).
  { apply Z.div_pos; lia. }
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply prefix_resource_state_zero__initialization.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply permutation_preserves_znth_bounds__initialization; eauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8.
  rewrite !Zlength_correct.
  f_equal.
  symmetry.
  exact (Permutation_length PreH1).
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
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in PreH3.
  subst served.
  replace (x - x) with 0 by lia.
  eapply prefix_resource_state_advance__resource_transitions.
  - lia.
  - exact PreH18.
  - intros suffix.
    apply can_print_all_cons_scarce_doubles__resource_transitions; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in *.
  subst served.
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)).
  pose proof (positive_page_div2_remainder__resource_transitions
    (Znth i sorted_pages_2 0) Hpage) as (Hq & Hr & Hdecomp & Hceil).
  destruct Hr as [Hr | Hr]; [lia |].
  eapply prefix_resource_state_advance__resource_transitions.
  - lia.
  - exact PreH18.
  - intros suffix.
    eapply can_print_all_cons_resource_step__resource_transitions.
    + lia.
    + exact PreH11.
    + exact PreH13.
    + exact Hq.
    + lia.
    + exact PreH3.
    + exact PreH1.
    + exact Hdecomp.
    + exact Hceil.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in *.
  subst served.
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)).
  pose proof (positive_page_div2_remainder__resource_transitions
    (Znth i sorted_pages_2 0) Hpage) as (Hq & Hr & Hdecomp & Hceil).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH17 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in *.
  subst served.
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)).
  pose proof (positive_page_div2_remainder__resource_transitions
    (Znth i sorted_pages_2 0) Hpage) as (Hq & Hr & Hdecomp & Hceil).
  assert (y = 0) by lia. subst y.
  eapply prefix_resource_state_advance__resource_transitions.
  - lia.
  - exact PreH20.
  - intros suffix.
    apply can_print_all_cons_odd_no_singles__resource_transitions; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH17 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in *.
  subst served.
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)).
  pose proof (positive_page_div2_remainder__resource_transitions
    (Znth i sorted_pages_2 0) Hpage) as (Hq & Hr & Hdecomp & Hceil).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH14 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in *.
  pose proof (positive_page_div2_remainder__resource_transitions
    (Znth i sorted_pages_2 0) Hpage) as (Hq & Hr & Hdecomp & Hceil).
  destruct Hr as [Hr | Hr]; exfalso; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_5_split_goal_1 : solver_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH14 i ltac:(lia)) as [Hpage _].
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)) in *.
  subst served.
  rewrite (positive_quot_eq_div__resource_transitions
    (Znth i sorted_pages_2 0) ltac:(lia)).
  pose proof (positive_page_div2_remainder__resource_transitions
    (Znth i sorted_pages_2 0) Hpage) as (Hq & Hr & Hdecomp & Hceil).
  destruct Hr as [Hr | Hr]; [|lia].
  eapply prefix_resource_state_advance__resource_transitions.
  - lia.
  - exact PreH17.
  - intros suffix.
    replace y with (y - 0) at 2 by lia.
    eapply can_print_all_cons_resource_step__resource_transitions; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst served.
  eapply spec_from_complete_prefix__early_exit.
  - rewrite PreH4. lia.
  - exact PreH8.
  - exact PreH10.
  - exact PreH13.
  - exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH16 i ltac:(lia)) as [Hpage _].
  rewrite Z.quot_div_nonneg in PreH1, PreH2, PreH3, PreH4 by lia.
  pose proof
    (positive_page_div2_remainder__resource_transitions
       (Znth i sorted_pages_2 0) Hpage) as Hrem.
  cbn zeta in Hrem.
  destruct Hrem as [Hq [[Hrem | Hrem] [Hpage_eq Hceil]]].
  - exfalso. nia.
  - exfalso. apply PreH1. exact Hrem.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_3_split_goal_1 : solver_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst served.
  eapply spec_from_prefix_stop__early_exit.
  - rewrite PreH8. lia.
  - exact PreH12.
  - exact PreH14.
  - exact PreH17.
  - exact PreH18.
  - exact PreH19.
  - apply single_page_infeasible__early_exit; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_4_split_goal_1 : solver_entail_wit_3_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst served.
  eapply spec_from_prefix_stop__early_exit.
  - rewrite PreH9. lia.
  - exact PreH13.
  - exact PreH15.
  - exact PreH18.
  - exact PreH19.
  - exact PreH20.
  - apply single_page_infeasible__early_exit; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_5_split_goal_1 : solver_entail_wit_3_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst served.
  eapply spec_from_prefix_stop__early_exit.
  - rewrite PreH9. lia.
  - exact PreH13.
  - exact PreH15.
  - exact PreH18.
  - exact PreH19.
  - exact PreH20.
  - apply single_page_infeasible__early_exit; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_5 : solver_entail_wit_3_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_5_split_goal_1.
Qed.
