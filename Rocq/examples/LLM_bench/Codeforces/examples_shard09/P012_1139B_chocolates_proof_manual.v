From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P012_1139B_chocolates_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P012_1139B_chocolates_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SuffixDominantState.
  replace ((n_pre - 1) + 1) with (Zlength values) by lia.
  refine (ex_intro _ (@nil Z) _).
  split.
  - exact (dominant_purchase_empty__initialization values).
  - split.
    + reflexivity.
    + split.
      * intros _. reflexivity.
      * intro H. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH3 k H).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH1.
  replace (i - 1 + 1) with i by lia.
  pose proof (PreH6 i ltac:(lia)) as Hstock.
  apply (suffix_dominant_prepend__backward_transitions
    values i total prev (Znth i values 0)).
  - lia.
  - exact PreH13.
  - lia.
  - intros z Hz k Hk.
    destruct Hz as [[Hzlen _] _].
    assert (Hslen : Zlength (sublist (i + 1) (Zlength values) values) = 0).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite Hzlen in Hk.
    lia.
  - intros z _ y Hy.
    unfold FeasiblePurchase in Hy.
    destruct Hy as [_ [Hybound _]].
    pose proof (Zlength_nonneg (sublist (i + 1) (Zlength values) values)).
    specialize (Hybound 0 ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth0_cons in Hybound.
    exact (proj2 Hybound).
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  specialize (PreH8 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 1 + 1) with i by lia.
  unfold SuffixDominantState in PreH15.
  destruct PreH15 as [x [Hdom [Htotal [Hem Hprev]]]].
  pose proof (PreH8 i ltac:(lia)) as Hstock.
  apply (suffix_dominant_prepend__backward_transitions
    values i total prev 0).
  - lia.
  - exists x. exact (conj Hdom (conj Htotal (conj Hem Hprev))).
  - lia.
  - intros z Hz k Hk. left. reflexivity.
  - intros z Hz y Hy.
    destruct Hdom as [Hxfeasible Hxdominant].
    destruct Hz as [Hzfeasible Hzdominant].
    destruct Hzfeasible as [Hzlen [Hzbound Hzorder]].
    assert (Hprevx : prev = Znth 0 x 0).
    { apply Hprev. rewrite <- PreH7. lia. }
    assert (Hspos : 0 < Zlength (sublist (i + 1) (Zlength values) values)).
    { rewrite Zlength_sublist by lia. lia. }
    destruct y as [| q y].
    + change (0 <= 0). lia.
    + pose proof
        (feasible_purchase_tail__backward_transitions
          (Znth i values 0)
          (sublist (i + 1) (Zlength values) values) (q :: y) Hy)
        as Htail.
      simpl in Htail.
      unfold FeasiblePurchase in Hy.
      destruct Hy as [_ [_ Hyorder]].
      destruct (Z.eq_dec q 0) as [-> | Hq0].
      * rewrite Znth0_cons. lia.
      * specialize (Hyorder 0 1 ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth0_cons in Hyorder.
        rewrite Znth_cons in Hyorder by lia.
        destruct Hyorder as [Hq | Hq].
        { contradiction. }
        replace (1 - 1) with 0 in Hq by lia.
        pose proof (Hzdominant y Htail 0 ltac:(lia)) as Hyz.
        pose proof (Hxdominant z (conj Hzlen (conj Hzbound Hzorder)) 0 ltac:(lia)) as Hzx.
        rewrite Znth0_cons.
        lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 1 + 1) with i by lia.
  unfold SuffixDominantState in PreH15.
  destruct PreH15 as [x [Hdom [Htotal [Hem Hprev]]]].
  apply (suffix_dominant_prepend__backward_transitions
    values i total prev (Znth i values 0)).
  - lia.
  - exists x. exact (conj Hdom (conj Htotal (conj Hem Hprev))).
  - lia.
  - intros z Hz k Hk.
    destruct Hdom as [Hxfeasible Hxdominant].
    destruct Hz as [Hzfeasible Hzdominant].
    destruct Hzfeasible as [Hzlen [Hzbound Hzorder]].
    assert (Hprevx : prev = Znth 0 x 0).
    { apply Hprev. rewrite <- PreH7. lia. }
    assert (Hspos : 0 < Zlength (sublist (i + 1) (Zlength values) values)).
    { rewrite <- Hzlen. lia. }
    assert (Hprevz : prev = Znth 0 z 0).
    { pose proof (Hxdominant z (conj Hzlen (conj Hzbound Hzorder)) 0 ltac:(lia)) as Hzx.
      pose proof (Hzdominant x Hxfeasible 0 ltac:(lia)) as Hxz.
      lia. }
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + right. lia.
    + specialize (Hzorder 0 k ltac:(lia)).
      destruct Hzorder as [Hzero | Hzlt].
      * lia.
      * right. lia.
  - intros z _ y Hy.
    unfold FeasiblePurchase in Hy.
    destruct Hy as [_ [Hybound _]].
    pose proof (Zlength_nonneg (sublist (i + 1) (Zlength values) values)).
    specialize (Hybound 0 ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth0_cons in Hybound.
    exact (proj2 Hybound).
Qed.

Lemma proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_5_split_goal_1 : solver_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 1 + 1) with i by lia.
  unfold SuffixDominantState in PreH15.
  destruct PreH15 as [x [Hdom [Htotal [Hem Hprev]]]].
  apply (suffix_dominant_prepend__backward_transitions
    values i total prev (prev - 1)).
  - lia.
  - exists x. exact (conj Hdom (conj Htotal (conj Hem Hprev))).
  - lia.
  - intros z Hz k Hk.
    destruct Hdom as [Hxfeasible Hxdominant].
    destruct Hz as [Hzfeasible Hzdominant].
    destruct Hzfeasible as [Hzlen [Hzbound Hzorder]].
    assert (Hprevx : prev = Znth 0 x 0).
    { apply Hprev. rewrite <- PreH7. lia. }
    assert (Hspos : 0 < Zlength (sublist (i + 1) (Zlength values) values)).
    { rewrite <- Hzlen. lia. }
    assert (Hprevz : prev = Znth 0 z 0).
    { pose proof (Hxdominant z (conj Hzlen (conj Hzbound Hzorder)) 0 ltac:(lia)) as Hzx.
      pose proof (Hzdominant x Hxfeasible 0 ltac:(lia)) as Hxz.
      lia. }
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + right. lia.
    + specialize (Hzorder 0 k ltac:(lia)).
      destruct Hzorder as [Hzero | Hzlt].
      * lia.
      * right. lia.
  - intros z Hz y Hy.
    destruct Hdom as [Hxfeasible Hxdominant].
    destruct Hz as [Hzfeasible Hzdominant].
    destruct Hzfeasible as [Hzlen [Hzbound Hzorder]].
    assert (Hprevx : prev = Znth 0 x 0).
    { apply Hprev. rewrite <- PreH7. lia. }
    assert (Hspos : 0 < Zlength (sublist (i + 1) (Zlength values) values)).
    { rewrite Zlength_sublist by lia. lia. }
    assert (Hprevz : prev = Znth 0 z 0).
    { pose proof (Hxdominant z (conj Hzlen (conj Hzbound Hzorder)) 0 ltac:(lia)) as Hzx.
      pose proof (Hzdominant x Hxfeasible 0 ltac:(lia)) as Hxz.
      lia. }
    destruct y as [| q y].
    + change (0 <= prev - 1). lia.
    + pose proof
        (feasible_purchase_tail__backward_transitions
          (Znth i values 0)
          (sublist (i + 1) (Zlength values) values) (q :: y) Hy)
        as Htail.
      simpl in Htail.
      unfold FeasiblePurchase in Hy.
      destruct Hy as [_ [_ Hyorder]].
      destruct (Z.eq_dec q 0) as [-> | Hq0].
      * rewrite Znth0_cons. lia.
      * specialize (Hyorder 0 1 ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth0_cons in Hyorder.
        rewrite Znth_cons in Hyorder by lia.
        destruct Hyorder as [Hq | Hq].
        { contradiction. }
        replace (1 - 1) with 0 in Hq by lia.
        pose proof (Hzdominant y Htail 0 ltac:(lia)) as Hyz.
        rewrite Znth0_cons.
        lia.
Qed.

Lemma proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_5_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  apply (suffix_dominant_state_to_spec__final_result values total prev).
  replace (i + 1) with 0 in PreH12 by lia.
  exact PreH12.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
