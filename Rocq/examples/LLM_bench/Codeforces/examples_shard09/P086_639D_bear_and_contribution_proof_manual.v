From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P086_639D_bear_and_contribution_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P086_639D_bear_and_contribution_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib.
Local Open Scope sac.

Lemma proof_of_hpush_entail_wit_1_split_goal_1 : hpush_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply push_sift_state_init__hpush_sift_up; [lia | lia | assumption].
Qed.

Lemma proof_of_hpush_entail_wit_1_split_goal_2 : hpush_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec q hs) as [Hq | Hq].
  - subst q. rewrite Znth_replace_Znth_Same by lia. lia.
  - rewrite Znth_replace_Znth_Diff by lia. apply PreH7. lia.
Qed.

Lemma proof_of_hpush_entail_wit_1_split_goal_3 : hpush_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__hpush_sift_up. lia.
Qed.

Lemma proof_of_hpush_entail_wit_1 : hpush_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpush_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_hpush_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_hpush_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_hpush_entail_wit_2_split_goal_1 : hpush_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13. lia.
Qed.

Lemma proof_of_hpush_entail_wit_2_split_goal_2 : hpush_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (unfold HeapParent; reflexivity).
Qed.

Lemma proof_of_hpush_entail_wit_2_split_goal_3 : hpush_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (pose proof (heap_parent_range__hpush_sift_up i ltac:(lia)) as Hr;
        unfold HeapParent in Hr; lia).
Qed.

Lemma proof_of_hpush_entail_wit_2_split_goal_4 : hpush_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (pose proof (heap_parent_range__hpush_sift_up i ltac:(lia)) as Hr;
        unfold HeapParent in Hr; lia).
Qed.

Lemma proof_of_hpush_entail_wit_2 : hpush_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpush_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_hpush_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_hpush_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_hpush_entail_wit_2_split_goal_4.
Qed.

Lemma proof_of_hpush_entail_wit_3_split_goal_1 : hpush_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (push_sift_state_swap__hpush_sift_up l cur_2 hs i p v_pre);
    try lia; assumption.
Qed.

Lemma proof_of_hpush_entail_wit_3_split_goal_2 : hpush_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec q i) as [Hqi | Hqi].
  - subst q.
    rewrite Znth_replace_Znth_Same
      by (repeat rewrite Zlength_replace_Znth__hpush_sift_up; lia).
    apply PreH16. lia.
  - rewrite Znth_replace_Znth_Diff
      by (repeat rewrite Zlength_replace_Znth__hpush_sift_up; lia).
    destruct (Z.eq_dec q p) as [Hqp | Hqp].
    + subst q. rewrite Znth_replace_Znth_Same by lia.
      apply PreH16. lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply PreH16. lia.
Qed.

Lemma proof_of_hpush_entail_wit_3_split_goal_3 : hpush_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth__hpush_sift_up. lia.
Qed.

Lemma proof_of_hpush_entail_wit_3 : hpush_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpush_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_hpush_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_hpush_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_hpush_return_wit_1_split_goal_1 : hpush_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13. lia.
Qed.

Lemma proof_of_hpush_return_wit_1_split_goal_2 : hpush_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PushSiftState in PreH14.
  destruct PreH14 as (_ & _ & Hperm & _ & _).
  exact Hperm.
Qed.

Lemma proof_of_hpush_return_wit_1_split_goal_3 : hpush_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (push_sift_state_to_heap_ordered__hpush_sift_up l cur hs i_2 v_pre PreH14).
  left. lia.
Qed.

Lemma proof_of_hpush_return_wit_1 : hpush_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpush_return_wit_1_split_goal_1.
  - Goal_apply proof_of_hpush_return_wit_1_split_goal_2.
  - Goal_apply proof_of_hpush_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_hpush_return_wit_2_split_goal_1 : hpush_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_hpush_return_wit_2_split_goal_2 : hpush_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PushSiftState in PreH17.
  destruct PreH17 as (_ & _ & Hperm & _ & _).
  exact Hperm.
Qed.

Lemma proof_of_hpush_return_wit_2_split_goal_3 : hpush_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (push_sift_state_to_heap_ordered__hpush_sift_up l cur hs i_2 v_pre PreH17).
  right. rewrite <- PreH11. exact PreH1.
Qed.

Lemma proof_of_hpush_return_wit_2 : hpush_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpush_return_wit_2_split_goal_1.
  - Goal_apply proof_of_hpush_return_wit_2_split_goal_2.
  - Goal_apply proof_of_hpush_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_hpop_entail_wit_1 : hpop_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists (replace_Znth 0 (Znth (hs - 1) l 0) l).
  split_pure_spatial.
  - cancel. cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption;
      try (rewrite Zlength_replace_Znth; lia).
    + intros q Hq.
      apply (heap_root_is_max__hpop_sift_left_child l hs q); assumption.
    + intros q Hq.
      apply (pop_init_bounds__hpop_sift_left_child l hs cap q);
        try lia; assumption.
    + apply (pop_sift_state_init__hpop_sift_left_child l hs cap);
        try lia; assumption.
Qed.

Lemma proof_of_hpop_entail_wit_2_1_split_goal_1 : hpop_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst i.
  apply pop_sift_state_swap_right__hpop_sift_right_child; try lia.
  exact PreH18.
Qed.

Lemma proof_of_hpop_entail_wit_2_1_split_goal_2 : hpop_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. exact PreH10.
Qed.

Lemma proof_of_hpop_entail_wit_2_1 : hpop_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_2_split_goal_1 : hpop_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pop_sift_state_swap_right__hpop_sift_right_child; try lia.
  exact PreH18.
Qed.

Lemma proof_of_hpop_entail_wit_2_2_split_goal_2 : hpop_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. exact PreH10.
Qed.

Lemma proof_of_hpop_entail_wit_2_2 : hpop_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_3_split_goal_1 : hpop_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst i.
  apply pop_sift_state_swap_right__hpop_sift_right_child; try lia.
  exact PreH18.
Qed.

Lemma proof_of_hpop_entail_wit_2_3_split_goal_2 : hpop_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. exact PreH10.
Qed.

Lemma proof_of_hpop_entail_wit_2_3 : hpop_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_4_split_goal_1 : hpop_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pop_sift_state_swap_right__hpop_sift_right_child; try lia.
  exact PreH18.
Qed.

Lemma proof_of_hpop_entail_wit_2_4_split_goal_2 : hpop_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. exact PreH10.
Qed.

Lemma proof_of_hpop_entail_wit_2_4 : hpop_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_4_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_5_split_goal_1 : hpop_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap i);
    try assumption; try lia.
Qed.

Lemma proof_of_hpop_entail_wit_2_5_split_goal_2 : hpop_entail_wit_2_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth.
  exact PreH9.
Qed.

Lemma proof_of_hpop_entail_wit_2_5 : hpop_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_5_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_5_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_6_split_goal_1 : hpop_entail_wit_2_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  apply (pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap 0);
    try assumption; try lia.
Qed.

Lemma proof_of_hpop_entail_wit_2_6_split_goal_2 : hpop_entail_wit_2_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth.
  exact PreH9.
Qed.

Lemma proof_of_hpop_entail_wit_2_6 : hpop_entail_wit_2_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_6_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_6_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_7_split_goal_1 : hpop_entail_wit_2_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  apply (pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap 0);
    try assumption; try lia.
  intros _.
  replace (2 * 0 + 2) with (2 * 0 + 1 + 1) by lia.
  assumption.
Qed.

Lemma proof_of_hpop_entail_wit_2_7_split_goal_2 : hpop_entail_wit_2_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth.
  exact PreH10.
Qed.

Lemma proof_of_hpop_entail_wit_2_7 : hpop_entail_wit_2_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_7_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_7_split_goal_2.
Qed.

Lemma proof_of_hpop_entail_wit_2_8_split_goal_1 : hpop_entail_wit_2_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap i);
    try assumption; try lia.
  intros _.
  replace (2 * i + 2) with (2 * i + 1 + 1) by lia.
  assumption.
Qed.

Lemma proof_of_hpop_entail_wit_2_8_split_goal_2 : hpop_entail_wit_2_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth.
  exact PreH10.
Qed.

Lemma proof_of_hpop_entail_wit_2_8 : hpop_entail_wit_2_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_entail_wit_2_8_split_goal_1.
  - Goal_apply proof_of_hpop_entail_wit_2_8_split_goal_2.
Qed.

Lemma proof_of_hpop_return_wit_1_split_goal_1 : hpop_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH14. lia.
Qed.

Lemma proof_of_hpop_return_wit_1_split_goal_2 : hpop_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_hpop_return_wit_1_split_goal_3 : hpop_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_perm_extract_root__hpop_return.
  - eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_hpop_return_wit_1_split_goal_4 : hpop_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_sift_state_exit__hpop_return.
  - eassumption.
  - lia.
  - intros; solve [ assumption | lia ].
  - intros; solve [ assumption | lia ].
Qed.

Lemma proof_of_hpop_return_wit_1 : hpop_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_return_wit_1_split_goal_1.
  - Goal_apply proof_of_hpop_return_wit_1_split_goal_2.
  - Goal_apply proof_of_hpop_return_wit_1_split_goal_3.
  - Goal_apply proof_of_hpop_return_wit_1_split_goal_4.
Qed. 

Lemma proof_of_hpop_return_wit_2_split_goal_1 : hpop_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH14. lia.
Qed.

Lemma proof_of_hpop_return_wit_2_split_goal_2 : hpop_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_hpop_return_wit_2_split_goal_3 : hpop_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_perm_extract_root__hpop_return.
  - eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_hpop_return_wit_2_split_goal_4 : hpop_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_sift_state_exit__hpop_return.
  - eassumption.
  - lia.
  - intros; solve [ assumption | lia ].
  - intros; solve [ assumption | lia ].
Qed.

Lemma proof_of_hpop_return_wit_2 : hpop_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_return_wit_2_split_goal_1.
  - Goal_apply proof_of_hpop_return_wit_2_split_goal_2.
  - Goal_apply proof_of_hpop_return_wit_2_split_goal_3.
  - Goal_apply proof_of_hpop_return_wit_2_split_goal_4.
Qed. 

Lemma proof_of_hpop_return_wit_3_split_goal_1 : hpop_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH15. lia.
Qed.

Lemma proof_of_hpop_return_wit_3_split_goal_2 : hpop_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_hpop_return_wit_3_split_goal_3 : hpop_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_perm_extract_root__hpop_return.
  - eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_hpop_return_wit_3_split_goal_4 : hpop_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_sift_state_exit__hpop_return.
  - eassumption.
  - lia.
  - intros; solve [ assumption | lia ].
  - intros; solve [ assumption | lia ].
Qed.

Lemma proof_of_hpop_return_wit_3 : hpop_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_return_wit_3_split_goal_1.
  - Goal_apply proof_of_hpop_return_wit_3_split_goal_2.
  - Goal_apply proof_of_hpop_return_wit_3_split_goal_3.
  - Goal_apply proof_of_hpop_return_wit_3_split_goal_4.
Qed. 

Lemma proof_of_hpop_return_wit_4_split_goal_1 : hpop_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH15. lia.
Qed.

Lemma proof_of_hpop_return_wit_4_split_goal_2 : hpop_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_hpop_return_wit_4_split_goal_3 : hpop_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_perm_extract_root__hpop_return.
  - eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_hpop_return_wit_4_split_goal_4 : hpop_return_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_sift_state_exit__hpop_return.
  - eassumption.
  - lia.
  - intros; solve [ assumption | lia ].
  - intros; solve [ assumption | lia ].
Qed.

Lemma proof_of_hpop_return_wit_4 : hpop_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_return_wit_4_split_goal_1.
  - Goal_apply proof_of_hpop_return_wit_4_split_goal_2.
  - Goal_apply proof_of_hpop_return_wit_4_split_goal_3.
  - Goal_apply proof_of_hpop_return_wit_4_split_goal_4.
Qed. 

Lemma proof_of_hpop_return_wit_5_split_goal_1 : hpop_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_hpop_return_wit_5_split_goal_2 : hpop_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_hpop_return_wit_5_split_goal_3 : hpop_return_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_perm_extract_root__hpop_return.
  - eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_hpop_return_wit_5_split_goal_4 : hpop_return_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_sift_state_exit__hpop_return.
  - eassumption.
  - lia.
  - intros; solve [ assumption | lia ].
  - intros; solve [ assumption | lia ].
Qed.

Lemma proof_of_hpop_return_wit_5 : hpop_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_return_wit_5_split_goal_1.
  - Goal_apply proof_of_hpop_return_wit_5_split_goal_2.
  - Goal_apply proof_of_hpop_return_wit_5_split_goal_3.
  - Goal_apply proof_of_hpop_return_wit_5_split_goal_4.
Qed. 

Lemma proof_of_hpop_return_wit_6_split_goal_1 : hpop_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_hpop_return_wit_6_split_goal_2 : hpop_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_hpop_return_wit_6_split_goal_3 : hpop_return_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_perm_extract_root__hpop_return.
  - eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_hpop_return_wit_6_split_goal_4 : hpop_return_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pop_sift_state_exit__hpop_return.
  - eassumption.
  - lia.
  - intros; solve [ assumption | lia ].
  - intros; solve [ assumption | lia ].
Qed.

Lemma proof_of_hpop_return_wit_6 : hpop_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hpop_return_wit_6_split_goal_1.
  - Goal_apply proof_of_hpop_return_wit_6_split_goal_2.
  - Goal_apply proof_of_hpop_return_wit_6_split_goal_3.
  - Goal_apply proof_of_hpop_return_wit_6_split_goal_4.
Qed. 

Lemma proof_of_sift_candidates_entail_wit_1_split_goal_1 : sift_candidates_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply sift_state_init__sift_cand_step; [lia | exact PreH7].
Qed.

Lemma proof_of_sift_candidates_entail_wit_1_split_goal_2 : sift_candidates_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; apply PreH8; lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_1 : sift_candidates_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sift_candidates_entail_wit_1_split_goal_2.
Qed. 

Lemma proof_of_sift_candidates_entail_wit_2_1_split_goal_1 : sift_candidates_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hzt : Zlength t_2 = Zlength t0).
  { destruct PreH13 as [[_ [Ht _]] _]. exact Ht. }
  apply sift_state_swap__sift_cand_step.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply heap_parent_child__sift_cand_step; [lia | right; lia].
  - lia.
  - intros s Hs1 Hs2 Hps.
    pose proof (heap_parent_inv__sift_cand_step s root Hs1 Hps) as Hinv.
    destruct Hinv as [Hinv | Hinv]; subst s.
    + lia.
    + replace (2 * root + 2) with (2 * root + 1 + 1) by lia. lia.
  - exact PreH13.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_1_split_goal_2 : sift_candidates_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_1_split_goal_3 : sift_candidates_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_1 : sift_candidates_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_1_split_goal_3.
Qed. 

Lemma proof_of_sift_candidates_entail_wit_2_2_split_goal_1 : sift_candidates_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hzt : Zlength t_2 = Zlength t0).
  { destruct PreH12 as [[_ [Ht _]] _]. exact Ht. }
  apply sift_state_swap__sift_cand_step.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply heap_parent_child__sift_cand_step; [lia | left; lia].
  - lia.
  - intros s Hs1 Hs2 Hps.
    pose proof (heap_parent_inv__sift_cand_step s root Hs1 Hps) as Hinv.
    destruct Hinv as [Hinv | Hinv]; subst s.
    + lia.
    + lia.
  - exact PreH12.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_2_split_goal_2 : sift_candidates_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_2_split_goal_3 : sift_candidates_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_2 : sift_candidates_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_2_split_goal_3.
Qed. 

Lemma proof_of_sift_candidates_entail_wit_2_3_split_goal_1 : sift_candidates_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hzt : Zlength t_2 = Zlength t0).
  { destruct PreH13 as [[_ [Ht _]] _]. exact Ht. }
  apply sift_state_swap__sift_cand_step.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply heap_parent_child__sift_cand_step; [lia | left; lia].
  - lia.
  - intros s Hs1 Hs2 Hps.
    pose proof (heap_parent_inv__sift_cand_step s root Hs1 Hps) as Hinv.
    destruct Hinv as [Hinv | Hinv]; subst s.
    + lia.
    + replace (2 * root + 2) with (2 * root + 1 + 1) by lia. lia.
  - exact PreH13.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_3_split_goal_2 : sift_candidates_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_3_split_goal_3 : sift_candidates_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sift_candidates_entail_wit_2_3 : sift_candidates_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_sift_candidates_entail_wit_2_3_split_goal_3.
Qed. 

Lemma proof_of_sift_candidates_return_wit_1_split_goal_1 : sift_candidates_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_1_split_goal_2 : sift_candidates_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [Hzip [_ [Hbs _]]].
  destruct Hzip as [Hb0 [Ht0 _]].
  replace cap with (Zlength b0) by lia.
  exact Hbs.
Qed.

Lemma proof_of_sift_candidates_return_wit_1_split_goal_3 : sift_candidates_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [Hzip [Hts _]].
  destruct Hzip as [_ [Ht0 _]].
  replace cap with (Zlength t0) by lia.
  exact Hts.
Qed.

Lemma proof_of_sift_candidates_return_wit_1_split_goal_4 : sift_candidates_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [Hzip _].
  exact Hzip.
Qed.

Lemma proof_of_sift_candidates_return_wit_1_split_goal_5 : sift_candidates_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre + 1) root_pre root PreH13).
  intros child Hc0 Hcs Hp.
  destruct (heap_parent_children__sift_cand_exit child root Hc0 Hp) as [-> | ->]; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_1 : sift_candidates_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sift_candidates_return_wit_1_split_goal_2.
  - Goal_apply proof_of_sift_candidates_return_wit_1_split_goal_3.
  - Goal_apply proof_of_sift_candidates_return_wit_1_split_goal_4.
  - Goal_apply proof_of_sift_candidates_return_wit_1_split_goal_5.
Qed.

Lemma proof_of_sift_candidates_return_wit_2_split_goal_1 : sift_candidates_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH11; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_2_split_goal_2 : sift_candidates_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH12 as [Hzip [_ [Hbs _]]].
  destruct Hzip as [Hb0 [Ht0 _]].
  replace cap with (Zlength b0) by lia.
  exact Hbs.
Qed.

Lemma proof_of_sift_candidates_return_wit_2_split_goal_3 : sift_candidates_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH12 as [Hzip [Hts _]].
  destruct Hzip as [_ [Ht0 _]].
  replace cap with (Zlength t0) by lia.
  exact Hts.
Qed.

Lemma proof_of_sift_candidates_return_wit_2_split_goal_4 : sift_candidates_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH12 as [Hzip _].
  exact Hzip.
Qed.

Lemma proof_of_sift_candidates_return_wit_2_split_goal_5 : sift_candidates_return_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre + 1) root_pre root PreH12).
  intros child Hc0 Hcs Hp.
  destruct (heap_parent_children__sift_cand_exit child root Hc0 Hp) as [-> | ->]; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_2 : sift_candidates_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_return_wit_2_split_goal_1.
  - Goal_apply proof_of_sift_candidates_return_wit_2_split_goal_2.
  - Goal_apply proof_of_sift_candidates_return_wit_2_split_goal_3.
  - Goal_apply proof_of_sift_candidates_return_wit_2_split_goal_4.
  - Goal_apply proof_of_sift_candidates_return_wit_2_split_goal_5.
Qed.

Lemma proof_of_sift_candidates_return_wit_3_split_goal_1 : sift_candidates_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_3_split_goal_2 : sift_candidates_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [Hzip [_ [Hbs _]]].
  destruct Hzip as [Hb0 [Ht0 _]].
  replace cap with (Zlength b0) by lia.
  exact Hbs.
Qed.

Lemma proof_of_sift_candidates_return_wit_3_split_goal_3 : sift_candidates_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [Hzip [Hts _]].
  destruct Hzip as [_ [Ht0 _]].
  replace cap with (Zlength t0) by lia.
  exact Hts.
Qed.

Lemma proof_of_sift_candidates_return_wit_3_split_goal_4 : sift_candidates_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [Hzip _].
  exact Hzip.
Qed.

Lemma proof_of_sift_candidates_return_wit_3_split_goal_5 : sift_candidates_return_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre + 1) root_pre root PreH13).
  intros child Hc0 Hcs Hp.
  destruct (heap_parent_children__sift_cand_exit child root Hc0 Hp) as [-> | ->]; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_3 : sift_candidates_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_return_wit_3_split_goal_1.
  - Goal_apply proof_of_sift_candidates_return_wit_3_split_goal_2.
  - Goal_apply proof_of_sift_candidates_return_wit_3_split_goal_3.
  - Goal_apply proof_of_sift_candidates_return_wit_3_split_goal_4.
  - Goal_apply proof_of_sift_candidates_return_wit_3_split_goal_5.
Qed.

Lemma proof_of_sift_candidates_return_wit_4_split_goal_1 : sift_candidates_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_4_split_goal_2 : sift_candidates_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [Hzip [_ [Hbs _]]].
  destruct Hzip as [Hb0 [Ht0 _]].
  replace cap with (Zlength b0) by lia.
  exact Hbs.
Qed.

Lemma proof_of_sift_candidates_return_wit_4_split_goal_3 : sift_candidates_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [Hzip [Hts _]].
  destruct Hzip as [_ [Ht0 _]].
  replace cap with (Zlength t0) by lia.
  exact Hts.
Qed.

Lemma proof_of_sift_candidates_return_wit_4_split_goal_4 : sift_candidates_return_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [Hzip _].
  exact Hzip.
Qed.

Lemma proof_of_sift_candidates_return_wit_4_split_goal_5 : sift_candidates_return_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre + 1) root_pre root PreH10).
  intros child Hc0 Hcs Hp.
  destruct (heap_parent_children__sift_cand_exit child root Hc0 Hp) as [-> | ->]; lia.
Qed.

Lemma proof_of_sift_candidates_return_wit_4 : sift_candidates_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_candidates_return_wit_4_split_goal_1.
  - Goal_apply proof_of_sift_candidates_return_wit_4_split_goal_2.
  - Goal_apply proof_of_sift_candidates_return_wit_4_split_goal_3.
  - Goal_apply proof_of_sift_candidates_return_wit_4_split_goal_4.
  - Goal_apply proof_of_sift_candidates_return_wit_4_split_goal_5.
Qed.

Lemma proof_of_sort_candidates_safety_wit_1_split_goal_1 : sort_candidates_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (quot2_bounds__sort_build_phase n_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_candidates_safety_wit_1_split_goal_2 : sort_candidates_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (quot2_bounds__sort_build_phase n_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_candidates_safety_wit_1 : sort_candidates_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_candidates_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_candidates_entail_wit_1_split_goal_1 : sort_candidates_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply heap_ordered_from_half__sort_build_phase; lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_1_split_goal_2 : sort_candidates_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply zip_perm_refl__sort_build_phase. lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_1_split_goal_3 : sort_candidates_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. apply PreH5. lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_1_split_goal_4 : sort_candidates_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (quot2_bounds__sort_build_phase n_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_1 : sort_candidates_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_sort_candidates_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_sort_candidates_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_sort_candidates_entail_wit_2_split_goal_1 : sort_candidates_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (n_pre - 1 + 1) with n_pre by lia.
  exact PreH10.
Qed.

Lemma proof_of_sort_candidates_entail_wit_2_split_goal_2 : sort_candidates_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. apply PreH8. lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_2_split_goal_3 : sort_candidates_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (quot2_bounds__sort_build_phase n_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_2 : sort_candidates_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_sort_candidates_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_sort_candidates_entail_wit_3_split_goal_1 : sort_candidates_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (root - 1 + 1) with root by lia.
  replace (n_pre - 1 + 1) with n_pre in PreH3 by lia.
  exact PreH3.
Qed.

Lemma proof_of_sort_candidates_entail_wit_3_split_goal_2 : sort_candidates_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (zip_perm_trans__sort_build_phase t0 b0 t_2 b_2 t1 b1 PreH16 PreH4).
Qed.

Lemma proof_of_sort_candidates_entail_wit_3_split_goal_3 : sort_candidates_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. apply PreH7. lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_3 : sort_candidates_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_sort_candidates_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_sort_candidates_entail_wit_4_split_goal_1 : sort_candidates_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply heap_sort_state_full__sort_build_phase. lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_4_split_goal_2 : sort_candidates_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HeapOrdered.
  assert (Hroot : root + 1 = 0) by lia.
  rewrite <- Hroot.
  exact PreH10.
Qed.

Lemma proof_of_sort_candidates_entail_wit_4_split_goal_3 : sort_candidates_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. apply PreH8. lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_4 : sort_candidates_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_sort_candidates_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_sort_candidates_entail_wit_5_split_goal_1 : sort_candidates_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (n_pre - 1 + 1) with n_pre by lia.
  exact PreH7.
Qed.

Lemma proof_of_sort_candidates_entail_wit_5_split_goal_2 : sort_candidates_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5; lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_5 : sort_candidates_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_5_split_goal_2.
Qed. 

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_1 : sort_candidates_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (heap_sort_state_swap__sort_extract_phase t_2 n_pre hi
           PreH6 ltac:(lia) PreH5 PreH10 PreH11).
Qed.

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_2 : sort_candidates_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (hi - 1 + 1) with hi by lia.
  replace (0 + 1) with 1 by lia.
  apply (heap_ordered_from_swap__sort_extract_phase t_2 n_pre hi
           PreH6 ltac:(lia) PreH5 PreH10).
Qed.

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_3 : sort_candidates_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply zip_perm_swap0__sort_extract_phase; [ exact PreH9 | lia ].
Qed.

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_4 : sort_candidates_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !swap_Znth__sort_extract_phase by lia.
  destruct (Z.eq_dec q hi) as [Hqh | Hqh].
  - apply PreH8; lia.
  - destruct (Z.eq_dec q 0) as [Hq0 | Hq0].
    + apply PreH8; lia.
    + apply PreH8; lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_5 : sort_candidates_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth__sort_extract_phase.
  exact PreH7.
Qed.

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_6 : sort_candidates_entail_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Zlength_replace_Znth__sort_extract_phase.
  exact PreH6.
Qed.

Lemma proof_of_sort_candidates_entail_wit_6_split_goal_7 : sort_candidates_entail_wit_6_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same
    by (rewrite Zlength_replace_Znth__sort_extract_phase; lia).
  reflexivity.
Qed.

Lemma proof_of_sort_candidates_entail_wit_6 : sort_candidates_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_4.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_5.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_6.
  - Goal_apply proof_of_sort_candidates_entail_wit_6_split_goal_7.
Qed. 

Lemma proof_of_sort_candidates_entail_wit_7_split_goal_1 : sort_candidates_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (hi - 1 + 1) with hi in PreH5, PreH6 by lia.
  destruct PreH4 as [Zb0 [Zt1 [Zb1 Zperm]]].
  apply (heap_sort_state_after_sift__sort_extract_phase t_2 b_2 t1 b1 n_pre hi
           PreH13 PreH14 PreH1 PreH2 ltac:(lia) Zperm PreH5 PreH6 PreH18).
Qed.

Lemma proof_of_sort_candidates_entail_wit_7_split_goal_2 : sort_candidates_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_candidates_entail_wit_7_split_goal_3 : sort_candidates_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (zip_perm_trans__sort_extract_phase t0 b0 t_2 b_2 t1 b1 PreH16 PreH4).
Qed.

Lemma proof_of_sort_candidates_entail_wit_7_split_goal_4 : sort_candidates_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7; lia.
Qed.

Lemma proof_of_sort_candidates_entail_wit_7 : sort_candidates_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_sort_candidates_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_sort_candidates_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_sort_candidates_entail_wit_7_split_goal_4.
Qed. 

Lemma proof_of_sort_candidates_return_wit_1_split_goal_1 : sort_candidates_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8; lia.
Qed.

Lemma proof_of_sort_candidates_return_wit_1_split_goal_2 : sort_candidates_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (heap_sort_done_nondecreasing__sort_extract_phase t n_pre hi
           PreH6 PreH4 PreH1 PreH11).
Qed.

Lemma proof_of_sort_candidates_return_wit_1 : sort_candidates_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_candidates_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_candidates_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_sort_candidates_partial_solve_wit_1_pure_split_goal_1 : sort_candidates_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; apply PreH12; lia).
Qed.

Lemma proof_of_sort_candidates_partial_solve_wit_1_pure : sort_candidates_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_candidates_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_sort_candidates_partial_solve_wit_10_pure_split_goal_1 : sort_candidates_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_candidates_partial_solve_wit_10_pure : sort_candidates_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_candidates_partial_solve_wit_10_pure_split_goal_1.
Qed. 

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 i ltac:(lia)) as Hshb.
  destruct (rem5_quot5_spec__solver_safety_cand_a (j - Znth i sh 0)) as [_ Hr].
  lia.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 i ltac:(lia)) as Hshb.
  destruct (rem5_quot5_spec__solver_safety_cand_a (j - Znth i sh 0)) as [_ Hr].
  lia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_27_split_goal_1 : solver_safety_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH24 i ltac:(lia)) as Hshb.
  destruct (rem5_quot5_spec__solver_safety_cand_a (j - Znth i sh 0)) as [_ Hr].
  lia.
Qed.

Lemma proof_of_solver_safety_wit_27_split_goal_2 : solver_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH24 i ltac:(lia)) as Hshb.
  destruct (rem5_quot5_spec__solver_safety_cand_a (j - Znth i sh 0)) as [_ Hr].
  lia.
Qed.

Lemma proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_27_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 i ltac:(lia)) as Hshb.
  pose proof (rem5_shift_bound__solver_safety_cand_a (j - Znth i sh 0)) as Hm.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 i ltac:(lia)) as Hshb.
  pose proof (rem5_shift_bound__solver_safety_cand_a (j - Znth i sh 0)) as Hm.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_34_split_goal_1 : solver_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH24 i ltac:(lia)) as Hshb.
  pose proof (rem5_shift_bound__solver_safety_cand_a (j - Znth i sh 0)) as Hm.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_34_split_goal_2 : solver_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH24 i ltac:(lia)) as Hshb.
  pose proof (rem5_shift_bound__solver_safety_cand_a (j - Znth i sh 0)) as Hm.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_35_split_goal_1 : solver_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 i ltac:(lia)) as Hshb.
  pose proof (rem5_shift_bound__solver_safety_cand_a (j - Znth i sh 0)) as Hm.
  destruct (rem5_quot5_spec__solver_safety_cand_a
              (Znth i sh 0 + Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5 - j))
    as [Hqr Hqb].
  assert (Hq : 0 <= Z.quot (Znth i sh 0 + Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5 - j) 5
               <= 600000002) by lia.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_2 : solver_safety_wit_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 i ltac:(lia)) as Hshb.
  pose proof (rem5_shift_bound__solver_safety_cand_a (j - Znth i sh 0)) as Hm.
  destruct (rem5_quot5_spec__solver_safety_cand_a
              (Znth i sh 0 + Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5 - j))
    as [Hqr Hqb].
  assert (Hq : 0 <= Z.quot (Znth i sh 0 + Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5 - j) 5
               <= 600000002) by lia.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_36_split_goal_1 : solver_safety_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hsh : 1000000000 <= Znth i sh 0 <= 3000000000) by (apply PreH25; lia).
  pose proof (target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j Hsh (conj PreH14 PreH15)) as Hq.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_36_split_goal_2 : solver_safety_wit_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hsh : 1000000000 <= Znth i sh 0 <= 3000000000) by (apply PreH25; lia).
  pose proof (target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j Hsh (conj PreH14 PreH15)) as Hq.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_36_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_36_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_1 : solver_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - Znth i sh 0)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_2 : solver_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - Znth i sh 0)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_41_split_goal_1 : solver_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hsh : 1000000000 <= Znth i sh 0 <= 3000000000) by (apply PreH24; lia).
  pose proof (target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j Hsh (conj PreH14 PreH15)) as Hq.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - Znth i sh 0)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_41_split_goal_2 : solver_safety_wit_41_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hsh : 1000000000 <= Znth i sh 0 <= 3000000000) by (apply PreH24; lia).
  pose proof (target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j Hsh (conj PreH14 PreH15)) as Hq.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - Znth i sh 0)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_42_split_goal_1 : solver_safety_wit_42_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hsh : 1000000000 <= Znth i sh 0 <= 3000000000) by (apply PreH24; lia).
  pose proof (target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j Hsh (conj PreH14 PreH15)) as Hq.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_42_split_goal_2 : solver_safety_wit_42_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hsh : 1000000000 <= Znth i sh 0 <= 3000000000) by (apply PreH24; lia).
  pose proof (target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j Hsh (conj PreH14 PreH15)) as Hq.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_42_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_42_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_45_split_goal_1 : solver_safety_wit_45_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - Znth i sh 0)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_45_split_goal_2 : solver_safety_wit_45_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - Znth i sh 0)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_45_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_45_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_57_split_goal_1 : solver_safety_wit_57_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_57_split_goal_2 : solver_safety_wit_57_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_57_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_57_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_58_split_goal_1 : solver_safety_wit_58_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_58_split_goal_2 : solver_safety_wit_58_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_58_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_58_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_59_split_goal_1 : solver_safety_wit_59_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_59_split_goal_2 : solver_safety_wit_59_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_59_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_59_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_63_split_goal_1 : solver_safety_wit_63_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_63_split_goal_2 : solver_safety_wit_63_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_63_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_63_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_64_split_goal_1 : solver_safety_wit_64_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_64_split_goal_2 : solver_safety_wit_64_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_64_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_64_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_65_split_goal_1 : solver_safety_wit_65_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_2 : solver_safety_wit_65_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hst : 1000000000 <= Znth i st 0 <= 3000000004).
  { match goal with
    | H : forall q : Z, 0 <= q < _ -> (1000000000 <= Znth q st 0 <= _ /\ _) /\ _ |- _ =>
        destruct (H i ltac:(lia)) as [[? ?] ?]
    end. lia. }
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_69_split_goal_1 : solver_safety_wit_69_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH33 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_2 : solver_safety_wit_69_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH33 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_70_split_goal_1 : solver_safety_wit_70_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH33 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_70_split_goal_2 : solver_safety_wit_70_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH33 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_70_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_70_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_1 : solver_safety_wit_71_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH33 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_2 : solver_safety_wit_71_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH33 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_1 : solver_safety_wit_75_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH35 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_2 : solver_safety_wit_75_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH35 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_76_split_goal_1 : solver_safety_wit_76_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH35 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_76_split_goal_2 : solver_safety_wit_76_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH35 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_76_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_76_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_77_split_goal_1 : solver_safety_wit_77_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH35 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_77_split_goal_2 : solver_safety_wit_77_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH35 i ltac:(lia)) as Hst.
  pose proof (sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_77_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_77_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [|k IH]; intros x lo hi; simpl.
    - Exists (@nil Z).
      simpl.
      split_pure_spatial.
      + Intros_p Hlohi.
        cancel.
      + Intros_p Hlohi2.
        split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l.
      Exists (a :: l).
      simpl.
      cancel.
  }
  assert (Hshape_full :
    forall x n,
      Int64Array.full_shape x n
      |-- EX l : list Z, Int64Array.full x n l).
  {
    intros x n.
    unfold Int64Array.full_shape, Int64Array.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full shifted_pre n_pre).
  Intros sh.
  sep_apply_l_atomic (Hshape_full cand_t_pre n_pre).
  Intros ct.
  sep_apply_l_atomic (Hshape_full cand_base_pre n_pre).
  Intros cb.
  sep_apply_l_atomic (Hshape_full heap_pre n_pre).
  Intros hl.
  prop_apply_p (Int64Array.full_Zlength shifted_pre n_pre sh).
  Intros_p Hsh.
  prop_apply_p (Int64Array.full_Zlength cand_t_pre n_pre ct).
  Intros_p Hct.
  prop_apply_p (Int64Array.full_Zlength cand_base_pre n_pre cb).
  Intros_p Hcb.
  prop_apply_p (Int64Array.full_Zlength heap_pre n_pre hl).
  Intros_p Hhl.
  Exists hl cb ct sh.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia;
      try (unfold WCost; lia);
      try (unfold ShiftedPrefix; intros; lia).
Qed.

Lemma proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [|k IH]; intros x lo hi; simpl.
    - Exists (@nil Z).
      simpl.
      split_pure_spatial.
      + Intros_p Hlohi.
        cancel.
      + Intros_p Hlohi2.
        split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l.
      Exists (a :: l).
      simpl.
      cancel.
  }
  assert (Hshape_full :
    forall x n,
      Int64Array.full_shape x n
      |-- EX l : list Z, Int64Array.full x n l).
  {
    intros x n.
    unfold Int64Array.full_shape, Int64Array.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full shifted_pre n_pre).
  Intros sh.
  sep_apply_l_atomic (Hshape_full cand_t_pre n_pre).
  Intros ct.
  sep_apply_l_atomic (Hshape_full cand_base_pre n_pre).
  Intros cb.
  sep_apply_l_atomic (Hshape_full heap_pre n_pre).
  Intros hl.
  prop_apply_p (Int64Array.full_Zlength shifted_pre n_pre sh).
  Intros_p Hsh.
  prop_apply_p (Int64Array.full_Zlength cand_t_pre n_pre ct).
  Intros_p Hct.
  prop_apply_p (Int64Array.full_Zlength cand_base_pre n_pre cb).
  Intros_p Hcb.
  prop_apply_p (Int64Array.full_Zlength heap_pre n_pre hl).
  Intros_p Hhl.
  Exists hl cb ct sh.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia;
      try (unfold WCost; lia);
      try (unfold ShiftedPrefix; intros; lia).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply shifted_prefix_step__solver_shift_loop.
  - lia.
  - exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zlength_replace_Znth__solver_shift_loop.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply residue_best_zero__solver_shift_loop.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (PreH21 q_2 ltac:(lia)).
  pose proof (PreH10 q_2 ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace n_pre with i by lia.
  exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; apply PreH10; lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CandPrefix. intros q Hq. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH23; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_4.
Qed. 

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CandPrefix. intros q Hq. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH22; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_4 : solver_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_4.
Qed. 

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply cand_prefix_step__solver_cand_fill; try lia.
  - pose proof (PreH25 i ltac:(lia)) as [Hlo Hhi]. lia.
  - assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply cand_prefix_step__solver_cand_fill; try lia.
  - pose proof (PreH24 i ltac:(lia)) as [Hlo Hhi]. lia.
  - assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_3 : solver_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia. subst i.
  Exists b1 t1 hl_2 cb_2 ct_2 sh_2.
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia. subst i.
  Exists b1 t1 hl_2 cb_2 ct_2 sh_2.
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 0.
  split_pure_spatial.
  - cancel. cancel. cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (apply heap_ordered_zero__solver_postsort_sweep_init).
    all: try (symmetry; apply zsum_sublist_0_0__solver_postsort_sweep_init).
    all: try (apply heap_content_empty__solver_postsort_sweep_init).
    all: try (apply sweep_best_at_zero__solver_postsort_sweep_init; [lia | assumption]).
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 0.
  split_pure_spatial.
  - cancel. cancel. cancel. cancel. cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (apply heap_ordered_zero__solver_postsort_sweep_init).
    all: try (symmetry; apply zsum_sublist_0_0__solver_postsort_sweep_init).
    all: try (apply heap_content_empty__solver_postsort_sweep_init).
    all: try (apply sweep_best_at_zero__solver_postsort_sweep_init; [lia | assumption]).
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (k_pre + 1 - 1) with k_pre in * by lia.
  destruct PreH49 as [Hmin Hhsum].
  assert (Hlp : Zlength (sublist 0 (k_pre + 1) l1) = k_pre + 1)
    by (apply Zlength_sublist0; lia).
  assert (Hub : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) -> y <= Znth 0 l1 0).
  { intros y Hy.
    apply (Permutation_in _ (Permutation_sym PreH9)) in Hy.
    apply In_Znth__solver_heap_maintain in Hy as [q [Hq He]].
    rewrite Hlp in Hq.
    rewrite Znth_sublist0 in He by lia.
    rewrite <- He. apply PreH4. lia. }
  assert (Hpp : Permutation (Znth i sb_2 0 :: sublist 0 k_pre hl_2)
                            (Znth 0 l1 0 :: sublist 0 k_pre l1_2)).
  { apply Permutation_trans with (sublist 0 (k_pre + 1) l1).
    - apply Permutation_sym. apply PreH9.
    - apply PreH3. }
  assert (HzP : ZSum (sublist 0 (k_pre + 1) l1) - Znth 0 l1 0
                  = ZSum (sublist 0 k_pre l1_2)).
  { rewrite (zsum_permutation__solver_heap_maintain _ _ PreH3).
    rewrite zsum_cons__solver_heap_maintain. lia. }
  assert (Hsplit : sublist 0 (i + 1) sb_2 = sublist 0 i sb_2 ++ (Znth i sb_2 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i sb_2) by lia.
    rewrite (sublist_single 0 i sb_2) by lia. reflexivity. }
  assert (Hbold : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) ->
                    -600000000000 <= y <= 4000).
  { intros y [Hy | Hy].
    - subst y. specialize (PreH45 i). lia.
    - revert y Hy.
      apply sublist_In_bounds__solver_heap_maintain.
      + lia.
      + intros q Hq. apply PreH46. lia. }
  assert (Hbnew : forall y, In y (sublist 0 k_pre l1_2) -> -600000000000 <= y <= 4000).
  { intros y Hy. apply Hbold.
    apply (Permutation_in _ (Permutation_sym Hpp)). right. auto. }
  assert (Hlnew : Zlength (sublist 0 k_pre l1_2) = k_pre)
    by (apply Zlength_sublist0; lia).
  pose proof (zsum_bounds__solver_heap_maintain _ _ _ Hbnew) as [Hzlo Hzhi].
  rewrite Hlnew in Hzlo, Hzhi.
  assert (Hmsm : MinSubMultiset (sublist 0 (i + 1) sb_2) (sublist 0 k_pre l1_2)).
  { rewrite Hsplit.
    apply (min_sub_multiset_push_pop__solver_heap_maintain
             (sublist 0 i sb_2) (sublist 0 k_pre hl_2) (sublist 0 k_pre l1_2)
             (Znth i sb_2 0) (Znth 0 l1 0)); auto. }
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2.
  split_pure_spatial.
  - cancel; cancel; cancel; cancel; cancel; cancel; cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + intros q Hq.
      rewrite <- (Znth_sublist0 0 q k_pre l1_2) by lia.
      apply Hbnew. apply Znth_In__solver_heap_maintain. lia.
    + unfold HeapContent. split.
      * exact Hmsm.
      * exact HzP.
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hhk : hsize = k_pre) by lia.
  rewrite Hhk in *.
  replace (k_pre + 1 - 1) with k_pre in * by lia.
  destruct PreH50 as [Hmin Hhsum].
  assert (Hlp : Zlength (sublist 0 (k_pre + 1) l1) = k_pre + 1)
    by (apply Zlength_sublist0; lia).
  assert (Hub : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) -> y <= Znth 0 l1 0).
  { intros y Hy.
    apply (Permutation_in _ (Permutation_sym PreH9)) in Hy.
    apply In_Znth__solver_heap_maintain in Hy as [q [Hq He]].
    rewrite Hlp in Hq.
    rewrite Znth_sublist0 in He by lia.
    rewrite <- He. apply PreH4. lia. }
  assert (Hpp : Permutation (Znth i sb_2 0 :: sublist 0 k_pre hl_2)
                            (Znth 0 l1 0 :: sublist 0 k_pre l1_2)).
  { apply Permutation_trans with (sublist 0 (k_pre + 1) l1).
    - apply Permutation_sym. apply PreH9.
    - apply PreH3. }
  assert (HzP : ZSum (sublist 0 (k_pre + 1) l1) - Znth 0 l1 0
                  = ZSum (sublist 0 k_pre l1_2)).
  { rewrite (zsum_permutation__solver_heap_maintain _ _ PreH3).
    rewrite zsum_cons__solver_heap_maintain. lia. }
  assert (Hsplit : sublist 0 (i + 1) sb_2 = sublist 0 i sb_2 ++ (Znth i sb_2 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i sb_2) by lia.
    rewrite (sublist_single 0 i sb_2) by lia. reflexivity. }
  assert (Hbold : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) ->
                    -600000000000 <= y <= 4000).
  { intros y [Hy | Hy].
    - subst y. specialize (PreH46 i). lia.
    - revert y Hy.
      apply sublist_In_bounds__solver_heap_maintain.
      + lia.
      + intros q Hq. apply PreH47. lia. }
  assert (Hbnew : forall y, In y (sublist 0 k_pre l1_2) -> -600000000000 <= y <= 4000).
  { intros y Hy. apply Hbold.
    apply (Permutation_in _ (Permutation_sym Hpp)). right. auto. }
  assert (Hlnew : Zlength (sublist 0 k_pre l1_2) = k_pre)
    by (apply Zlength_sublist0; lia).
  pose proof (zsum_bounds__solver_heap_maintain _ _ _ Hbnew) as [Hzlo Hzhi].
  rewrite Hlnew in Hzlo, Hzhi.
  assert (Hmsm : MinSubMultiset (sublist 0 (i + 1) sb_2) (sublist 0 k_pre l1_2)).
  { rewrite Hsplit.
    apply (min_sub_multiset_push_pop__solver_heap_maintain
             (sublist 0 i sb_2) (sublist 0 k_pre hl_2) (sublist 0 k_pre l1_2)
             (Znth i sb_2 0) (Znth 0 l1 0)); auto. }
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2.
  split_pure_spatial.
  - cancel; cancel; cancel; cancel; cancel; cancel; cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + intros q Hq.
      rewrite <- (Znth_sublist0 0 q k_pre l1_2) by lia.
      apply Hbnew. apply Znth_In__solver_heap_maintain. lia.
    + unfold HeapContent. split.
      * exact Hmsm.
      * exact HzP.
Qed.

Lemma proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (k_pre + 1 - 1) with k_pre in * by lia.
  destruct PreH48 as [Hmin Hhsum].
  assert (Hlp : Zlength (sublist 0 (k_pre + 1) l1) = k_pre + 1)
    by (apply Zlength_sublist0; lia).
  assert (Hub : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) -> y <= Znth 0 l1 0).
  { intros y Hy.
    apply (Permutation_in _ (Permutation_sym PreH9)) in Hy.
    apply In_Znth__solver_heap_maintain in Hy as [q [Hq He]].
    rewrite Hlp in Hq.
    rewrite Znth_sublist0 in He by lia.
    rewrite <- He. apply PreH4. lia. }
  assert (Hpp : Permutation (Znth i sb_2 0 :: sublist 0 k_pre hl_2)
                            (Znth 0 l1 0 :: sublist 0 k_pre l1_2)).
  { apply Permutation_trans with (sublist 0 (k_pre + 1) l1).
    - apply Permutation_sym. apply PreH9.
    - apply PreH3. }
  assert (HzP : ZSum (sublist 0 (k_pre + 1) l1) - Znth 0 l1 0
                  = ZSum (sublist 0 k_pre l1_2)).
  { rewrite (zsum_permutation__solver_heap_maintain _ _ PreH3).
    rewrite zsum_cons__solver_heap_maintain. lia. }
  assert (Hsplit : sublist 0 (i + 1) sb_2 = sublist 0 i sb_2 ++ (Znth i sb_2 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i sb_2) by lia.
    rewrite (sublist_single 0 i sb_2) by lia. reflexivity. }
  assert (Hbold : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) ->
                    -600000000000 <= y <= 4000).
  { intros y [Hy | Hy].
    - subst y. specialize (PreH44 i). lia.
    - revert y Hy.
      apply sublist_In_bounds__solver_heap_maintain.
      + lia.
      + intros q Hq. apply PreH45. lia. }
  assert (Hbnew : forall y, In y (sublist 0 k_pre l1_2) -> -600000000000 <= y <= 4000).
  { intros y Hy. apply Hbold.
    apply (Permutation_in _ (Permutation_sym Hpp)). right. auto. }
  assert (Hlnew : Zlength (sublist 0 k_pre l1_2) = k_pre)
    by (apply Zlength_sublist0; lia).
  pose proof (zsum_bounds__solver_heap_maintain _ _ _ Hbnew) as [Hzlo Hzhi].
  rewrite Hlnew in Hzlo, Hzhi.
  assert (Hmsm : MinSubMultiset (sublist 0 (i + 1) sb_2) (sublist 0 k_pre l1_2)).
  { rewrite Hsplit.
    apply (min_sub_multiset_push_pop__solver_heap_maintain
             (sublist 0 i sb_2) (sublist 0 k_pre hl_2) (sublist 0 k_pre l1_2)
             (Znth i sb_2 0) (Znth 0 l1 0)); auto. }
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2.
  split_pure_spatial.
  - cancel; cancel; cancel; cancel; cancel; cancel; cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + intros q Hq.
      rewrite <- (Znth_sublist0 0 q k_pre l1_2) by lia.
      apply Hbnew. apply Znth_In__solver_heap_maintain. lia.
    + unfold HeapContent. split.
      * exact Hmsm.
      * exact HzP.
Qed.

Lemma proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hhk : hsize = k_pre) by lia.
  rewrite Hhk in *.
  replace (k_pre + 1 - 1) with k_pre in * by lia.
  destruct PreH49 as [Hmin Hhsum].
  assert (Hlp : Zlength (sublist 0 (k_pre + 1) l1) = k_pre + 1)
    by (apply Zlength_sublist0; lia).
  assert (Hub : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) -> y <= Znth 0 l1 0).
  { intros y Hy.
    apply (Permutation_in _ (Permutation_sym PreH9)) in Hy.
    apply In_Znth__solver_heap_maintain in Hy as [q [Hq He]].
    rewrite Hlp in Hq.
    rewrite Znth_sublist0 in He by lia.
    rewrite <- He. apply PreH4. lia. }
  assert (Hpp : Permutation (Znth i sb_2 0 :: sublist 0 k_pre hl_2)
                            (Znth 0 l1 0 :: sublist 0 k_pre l1_2)).
  { apply Permutation_trans with (sublist 0 (k_pre + 1) l1).
    - apply Permutation_sym. apply PreH9.
    - apply PreH3. }
  assert (HzP : ZSum (sublist 0 (k_pre + 1) l1) - Znth 0 l1 0
                  = ZSum (sublist 0 k_pre l1_2)).
  { rewrite (zsum_permutation__solver_heap_maintain _ _ PreH3).
    rewrite zsum_cons__solver_heap_maintain. lia. }
  assert (Hsplit : sublist 0 (i + 1) sb_2 = sublist 0 i sb_2 ++ (Znth i sb_2 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i sb_2) by lia.
    rewrite (sublist_single 0 i sb_2) by lia. reflexivity. }
  assert (Hbold : forall y, In y (Znth i sb_2 0 :: sublist 0 k_pre hl_2) ->
                    -600000000000 <= y <= 4000).
  { intros y [Hy | Hy].
    - subst y. specialize (PreH45 i). lia.
    - revert y Hy.
      apply sublist_In_bounds__solver_heap_maintain.
      + lia.
      + intros q Hq. apply PreH46. lia. }
  assert (Hbnew : forall y, In y (sublist 0 k_pre l1_2) -> -600000000000 <= y <= 4000).
  { intros y Hy. apply Hbold.
    apply (Permutation_in _ (Permutation_sym Hpp)). right. auto. }
  assert (Hlnew : Zlength (sublist 0 k_pre l1_2) = k_pre)
    by (apply Zlength_sublist0; lia).
  pose proof (zsum_bounds__solver_heap_maintain _ _ _ Hbnew) as [Hzlo Hzhi].
  rewrite Hlnew in Hzlo, Hzhi.
  assert (Hmsm : MinSubMultiset (sublist 0 (i + 1) sb_2) (sublist 0 k_pre l1_2)).
  { rewrite Hsplit.
    apply (min_sub_multiset_push_pop__solver_heap_maintain
             (sublist 0 i sb_2) (sublist 0 k_pre hl_2) (sublist 0 k_pre l1_2)
             (Znth i sb_2 0) (Znth 0 l1 0)); auto. }
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2.
  split_pure_spatial.
  - cancel; cancel; cancel; cancel; cancel; cancel; cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + intros q Hq.
      rewrite <- (Znth_sublist0 0 q k_pre l1_2) by lia.
      apply Hbnew. apply Znth_In__solver_heap_maintain. lia.
    + unfold HeapContent. split.
      * exact Hmsm.
      * exact HzP.
Qed.

Lemma proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst hsize.
  destruct PreH45 as [Hmin Hhsum].
  assert (Hlhl : Zlength (sublist 0 i hl) = i) by (apply Zlength_sublist0; lia).
  assert (Hlsb : Zlength (sublist 0 i sb) = i) by (apply Zlength_sublist0; lia).
  assert (Hperm0 : Permutation (sublist 0 i sb) (sublist 0 i hl)).
  { apply submultiset_full_perm__solver_heap_maintain.
    - apply Hmin.
    - lia. }
  assert (Hsplit : sublist 0 (i + 1) sb = sublist 0 i sb ++ (Znth i sb 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i sb) by lia.
    rewrite (sublist_single 0 i sb) by lia. reflexivity. }
  assert (Hperm1 : Permutation (sublist 0 (i + 1) sb) (sublist 0 (i + 1) l1)).
  { rewrite Hsplit.
    apply Permutation_trans with (Znth i sb 0 :: sublist 0 i sb).
    - apply Permutation_sym. apply Permutation_cons_append.
    - apply Permutation_sym. apply Permutation_trans with (Znth i sb 0 :: sublist 0 i hl).
      + apply PreH4.
      + apply perm_skip. apply Permutation_sym. apply Hperm0. }
  assert (Hzs : ZSum (sublist 0 i hl) + Znth i sb 0 = ZSum (sublist 0 (i + 1) l1)).
  { rewrite (zsum_permutation__solver_heap_maintain _ _ PreH4).
    rewrite zsum_cons__solver_heap_maintain. lia. }
  assert (Hbsb : forall y, In y (sublist 0 (i + 1) sb) -> -600000000000 <= y <= 4000).
  { apply sublist_In_bounds__solver_heap_maintain.
    - lia.
    - intros q Hq. specialize (PreH41 q). lia. }
  assert (Hbl1 : forall y, In y (sublist 0 (i + 1) l1) -> -600000000000 <= y <= 4000).
  { intros y Hy. apply Hbsb.
    apply (Permutation_in _ (Permutation_sym Hperm1)). auto. }
  assert (Hll1 : Zlength (sublist 0 (i + 1) l1) = i + 1) by (apply Zlength_sublist0; lia).
  pose proof (zsum_bounds__solver_heap_maintain _ _ _ Hbl1) as [Hzlo Hzhi].
  rewrite Hll1 in Hzlo, Hzhi.
  Exists sb st_2 l1 cb_2 ct_2 sh_2 (i + 1).
  split_pure_spatial.
  - cancel; cancel; cancel; cancel; cancel; cancel; cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + intros q Hq.
      rewrite <- (Znth_sublist0 0 q (i + 1) l1) by lia.
      apply Hbl1. apply Znth_In__solver_heap_maintain. lia.
    + unfold HeapContent. split.
      * apply min_sub_multiset_whole__solver_heap_maintain. exact Hperm1.
      * exact Hzs.
Qed.

Lemma proof_of_solver_entail_wit_8_6 : solver_entail_wit_8_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst hsize.
  destruct PreH44 as [Hmin Hhsum].
  assert (Hlhl : Zlength (sublist 0 i hl) = i) by (apply Zlength_sublist0; lia).
  assert (Hlsb : Zlength (sublist 0 i sb) = i) by (apply Zlength_sublist0; lia).
  assert (Hperm0 : Permutation (sublist 0 i sb) (sublist 0 i hl)).
  { apply submultiset_full_perm__solver_heap_maintain.
    - apply Hmin.
    - lia. }
  assert (Hsplit : sublist 0 (i + 1) sb = sublist 0 i sb ++ (Znth i sb 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i sb) by lia.
    rewrite (sublist_single 0 i sb) by lia. reflexivity. }
  assert (Hperm1 : Permutation (sublist 0 (i + 1) sb) (sublist 0 (i + 1) l1)).
  { rewrite Hsplit.
    apply Permutation_trans with (Znth i sb 0 :: sublist 0 i sb).
    - apply Permutation_sym. apply Permutation_cons_append.
    - apply Permutation_sym. apply Permutation_trans with (Znth i sb 0 :: sublist 0 i hl).
      + apply PreH4.
      + apply perm_skip. apply Permutation_sym. apply Hperm0. }
  assert (Hzs : ZSum (sublist 0 i hl) + Znth i sb 0 = ZSum (sublist 0 (i + 1) l1)).
  { rewrite (zsum_permutation__solver_heap_maintain _ _ PreH4).
    rewrite zsum_cons__solver_heap_maintain. lia. }
  assert (Hbsb : forall y, In y (sublist 0 (i + 1) sb) -> -600000000000 <= y <= 4000).
  { apply sublist_In_bounds__solver_heap_maintain.
    - lia.
    - intros q Hq. specialize (PreH40 q). lia. }
  assert (Hbl1 : forall y, In y (sublist 0 (i + 1) l1) -> -600000000000 <= y <= 4000).
  { intros y Hy. apply Hbsb.
    apply (Permutation_in _ (Permutation_sym Hperm1)). auto. }
  assert (Hll1 : Zlength (sublist 0 (i + 1) l1) = i + 1) by (apply Zlength_sublist0; lia).
  pose proof (zsum_bounds__solver_heap_maintain _ _ _ Hbl1) as [Hzlo Hzhi].
  rewrite Hll1 in Hzlo, Hzhi.
  Exists sb st_2 l1 cb_2 ct_2 sh_2 (i + 1).
  split_pure_spatial.
  - cancel; cancel; cancel; cancel; cancel; cancel; cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + intros q Hq.
      rewrite <- (Znth_sublist0 0 q (i + 1) l1) by lia.
      apply Hbl1. apply Znth_In__solver_heap_maintain. lia.
    + unfold HeapContent. split.
      * apply min_sub_multiset_whole__solver_heap_maintain. exact Hperm1.
      * exact Hzs.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2
                    st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum).
  destruct Hall as [Hks [Hsv [Htc [Hlo Hhi]]]]; try assumption.
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      first [ assumption | lia | reflexivity ].
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst hsize.
  assert (Hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2
                    st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum).
  destruct Hall as [Hks [Hsv [Htc [Hlo Hhi]]]]; try assumption.
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      first [ assumption | lia | reflexivity ].
Qed.

Lemma proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2
                    st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum).
  destruct Hall as [Hks [Hsv [Htc [Hlo Hhi]]]]; try assumption.
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      first [ assumption | lia | reflexivity ].
Qed.

Lemma proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst hsize.
  assert (Hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2
                    st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum).
  destruct Hall as [Hks [Hsv [Htc [Hlo Hhi]]]]; try assumption.
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      first [ assumption | lia | reflexivity ].
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1) total).
  { unfold SweepBest.
    apply (best_state_step__solver_best_update
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i)
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1))
             best total).
    - exact PreH44.
    - apply (sweep_set_step__solver_best_update contributions k_pre b_pre c_pre
               j st_2 sb_2 W i total); [ lia | exact PreH42 ].
    - lia.
    - left; lia. }
  destruct (Z_lt_le_dec k_pre (i + 1)) as [Hcase | Hcase].
  - Left.
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2.
    split_pure_spatial.
    + cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
    + split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
  - Right.
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2.
    split_pure_spatial.
    + cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
    + split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1) total).
  { unfold SweepBest.
    apply (best_state_step__solver_best_update
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i)
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1))
             best total).
    - exact PreH46.
    - apply (sweep_set_step__solver_best_update contributions k_pre b_pre c_pre
               j st_2 sb_2 W i total); [ lia | exact PreH44 ].
    - lia.
    - right; lia. }
  destruct (Z_lt_le_dec k_pre (i + 1)) as [Hcase | Hcase].
  - Left.
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2.
    split_pure_spatial.
    + cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
    + split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
  - Right.
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2.
    split_pure_spatial.
    + cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
    + split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
Qed.

Lemma proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1) best).
  { unfold SweepBest.
    apply (best_state_keep__solver_best_update
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i)
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1))
             best total).
    - exact PreH46.
    - apply (sweep_set_step__solver_best_update contributions k_pre b_pre c_pre
               j st_2 sb_2 W i total); [ lia | exact PreH44 ].
    - lia.
    - lia. }
  destruct (Z_lt_le_dec k_pre (i + 1)) as [Hcase | Hcase].
  - Left.
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2.
    split_pure_spatial.
    + cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
    + split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
  - Right.
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2.
    split_pure_spatial.
    + cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
    + split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
Qed.

Lemma proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1) best).
  { unfold SweepBest.
    apply (best_state_same__solver_best_update
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i)
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1))
             best).
    - apply (sweep_set_stall__solver_best_update contributions k_pre b_pre c_pre
               j st_2 sb_2 W i).
      lia.
    - exact PreH41. }
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsize_3.
  split_pure_spatial.
  - cancel ((( &( "hsize" ) )) # Int |-> hsize_3).
      cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
  - split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
Qed.

Lemma proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1) best).
  { unfold SweepBest.
    apply (best_state_same__solver_best_update
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i)
             (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i + 1))
             best).
    - apply (sweep_set_stall__solver_best_update contributions k_pre b_pre c_pre
               j st_2 sb_2 W i).
      lia.
    - exact PreH40. }
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsize_3.
  split_pure_spatial.
  - cancel ((( &( "hsize" ) )) # Int |-> hsize_3).
      cancel (Int64Array.full values_pre n_pre contributions).
      cancel (Int64Array.full shifted_pre n_pre sh_2).
      cancel (Int64Array.full cand_t_pre n_pre st_2).
      cancel (Int64Array.full cand_base_pre n_pre sb_2).
      cancel (Int64Array.full heap_pre n_pre hl_2).
  - split_pures; dump_pre_spatial; first [ assumption | lia | tauto ].
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  rewrite Hi in PreH40.
  apply (residue_best_of_sweep_best__solver_residue_rollup contributions sh_2 ct_2 cb_2
           st sb n_pre k_pre b_pre c_pre j W best); auto; try lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_2 : solver_entail_wit_11_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_3 : solver_entail_wit_11_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  rewrite Hi in PreH41.
  apply (residue_best_of_sweep_best__solver_residue_rollup contributions sh_2 ct_2 cb_2
           st sb n_pre k_pre b_pre c_pre j W best); auto; try lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_2 : solver_entail_wit_11_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_3 : solver_entail_wit_11_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_11_3_split_goal_1 : solver_entail_wit_11_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  rewrite Hi in PreH39.
  unfold SweepBest, BestState in PreH39.
  destruct PreH39 as [[_ Hnone] | [Hge _]]; [| lia].
  exfalso.
  destruct (sweep_set_inhabited__solver_residue_rollup contributions st sb
              k_pre b_pre c_pre j W n_pre ltac:(lia) ltac:(lia) ltac:(lia)) as [v Hv].
  exact (Hnone v Hv).
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_2 : solver_entail_wit_11_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_3 : solver_entail_wit_11_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_11_4_split_goal_1 : solver_entail_wit_11_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  rewrite Hi in PreH40.
  unfold SweepBest, BestState in PreH40.
  destruct PreH40 as [[_ Hnone] | [Hge _]]; [| lia].
  exfalso.
  destruct (sweep_set_inhabited__solver_residue_rollup contributions st sb
              k_pre b_pre c_pre j W n_pre ltac:(lia) ltac:(lia) ltac:(lia)) as [v Hv].
  exact (Hnone v Hv).
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_2 : solver_entail_wit_11_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_3 : solver_entail_wit_11_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hj : j = 5) by lia.
  subst j.
  unfold ResidueBest, BestState in PreH24.
  destruct PreH24 as [[Hm1 Hm2] | [Hm1 Hm2]]; [lia |].
  unfold Spec.
  refine (min_value_of_subset_ext__solver_final_spec _ _ _ _ Hm2).
  intros v.
  apply tie_cost_residue_cover__solver_final_spec.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_spatial : solver_entail_wit_12_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.full_to_full_shape shifted_pre n_pre sh).
  sep_apply_l_atomic (Int64Array.full_to_full_shape cand_t_pre n_pre ct).
  sep_apply_l_atomic (Int64Array.full_to_full_shape cand_base_pre n_pre cb).
  sep_apply_l_atomic (Int64Array.full_to_full_shape heap_pre n_pre hl).
  cancel (Int64Array.full_shape shifted_pre n_pre).
  cancel (Int64Array.full_shape cand_t_pre n_pre).
  cancel (Int64Array.full_shape cand_base_pre n_pre).
  cancel (Int64Array.full_shape heap_pre n_pre).
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hj : j = 5) by lia.
  subst j.
  unfold ResidueBest, BestState in PreH23.
  destruct PreH23 as [[Hm1 Hm2] | [Hm1 Hm2]]; [| lia].
  exfalso.
  destruct (tie_cost_inhabited__solver_final_spec contributions k_pre b_pre c_pre)
    as [v Hv]; try lia.
  apply (Hm2 v).
  apply (proj2 (tie_cost_residue_cover__solver_final_spec contributions k_pre b_pre c_pre v)).
  exact Hv.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_spatial : solver_entail_wit_12_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.full_to_full_shape shifted_pre n_pre sh).
  sep_apply_l_atomic (Int64Array.full_to_full_shape cand_t_pre n_pre ct).
  sep_apply_l_atomic (Int64Array.full_to_full_shape cand_base_pre n_pre cb).
  sep_apply_l_atomic (Int64Array.full_to_full_shape heap_pre n_pre hl).
  cancel (Int64Array.full_shape shifted_pre n_pre).
  cancel (Int64Array.full_shape cand_t_pre n_pre).
  cancel (Int64Array.full_shape cand_base_pre n_pre).
  cancel (Int64Array.full_shape heap_pre n_pre).
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure_split_goal_1 : solver_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros i Hi.
  match goal with
  | H : forall q : Z, 0 <= q < ?m -> ((1000000000 <= Znth q ct 0 /\ _) /\ _) /\ _ |- _ =>
      apply (H i ltac:(lia))
  end.
Qed.


Lemma proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_11_pure_split_goal_1.
Qed.


Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_1 : solver_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros i Hi.
  match goal with
  | H : forall q : Z, 0 <= q < ?m -> ((1000000000 <= Znth q ct 0 /\ _) /\ _) /\ _ |- _ =>
      apply (H i ltac:(lia))
  end.
Qed.


Lemma proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_1.
Qed.


Lemma proof_of_solver_partial_solve_wit_17_pure_split_goal_1 : solver_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros idx Hidx.
  match goal with
  | H : forall q : Z, 0 <= q < ?m -> (-600000000000 <= Znth q hl 0 /\ _) |- _ =>
      destruct (H idx ltac:(lia))
  end.
  lia.
Qed.


Lemma proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_17_pure_split_goal_1.
Qed.


Lemma proof_of_solver_partial_solve_wit_18_pure_split_goal_1 : solver_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros idx Hidx.
  match goal with
  | H : forall q : Z, 0 <= q < ?m -> (-600000000000 <= Znth q hl 0 /\ _) |- _ =>
      destruct (H idx ltac:(lia))
  end.
  lia.
Qed.


Lemma proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_18_pure_split_goal_1.
Qed.


Lemma proof_of_solver_partial_solve_wit_19_pure_split_goal_1 : solver_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros idx Hidx.
  match goal with
  | H : forall q : Z, 0 <= q < ?m -> (-600000000000 <= Znth q hl 0 /\ _) |- _ =>
      destruct (H idx ltac:(lia))
  end.
  lia.
Qed.


Lemma proof_of_solver_partial_solve_wit_19_pure : solver_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_19_pure_split_goal_1.
Qed.


Lemma proof_of_solver_partial_solve_wit_20_pure_split_goal_1 : solver_partial_solve_wit_20_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros idx Hidx.
  match goal with
  | H : forall q : Z, 0 <= q < ?m -> (-600000000000 <= Znth q hl 0 /\ _) |- _ =>
      destruct (H idx ltac:(lia))
  end.
  lia.
Qed.


Lemma proof_of_solver_partial_solve_wit_20_pure : solver_partial_solve_wit_20_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_20_pure_split_goal_1.
Qed.


Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_1 : solver_partial_solve_wit_21_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_2 : solver_partial_solve_wit_21_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_3 : solver_partial_solve_wit_21_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_4 : solver_partial_solve_wit_21_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_5 : solver_partial_solve_wit_21_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_6 : solver_partial_solve_wit_21_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH61 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH60 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_7 : solver_partial_solve_wit_21_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH61 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH60 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_5.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_6.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_7.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_1 : solver_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH47; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_2 : solver_partial_solve_wit_22_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH47; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_3 : solver_partial_solve_wit_22_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH47; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_4 : solver_partial_solve_wit_22_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH47; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_5 : solver_partial_solve_wit_22_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_6 : solver_partial_solve_wit_22_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH62 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH61 i_2 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_7 : solver_partial_solve_wit_22_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH62 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH61 i_2 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure : solver_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_5.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_6.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_7.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_1 : solver_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_2 : solver_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_3 : solver_partial_solve_wit_23_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_4 : solver_partial_solve_wit_23_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_5 : solver_partial_solve_wit_23_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_6 : solver_partial_solve_wit_23_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH60 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH59 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_7 : solver_partial_solve_wit_23_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH60 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH59 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_5.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_6.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_7.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_1 : solver_partial_solve_wit_24_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH46; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_2 : solver_partial_solve_wit_24_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH46; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_3 : solver_partial_solve_wit_24_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH46; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_4 : solver_partial_solve_wit_24_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (Znth hsize sb 0) with (Znth i_2 sb 0) by (rewrite PreH46; reflexivity).
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_5 : solver_partial_solve_wit_24_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_6 : solver_partial_solve_wit_24_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH61 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH60 i_2 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_7 : solver_partial_solve_wit_24_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (zsum_permutation__solver_hpop_call_pre _ _ PreH24).
  rewrite zsum_cons__solver_hpop_call_pre.
  pose proof (zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000
                ltac:(lia)
                ltac:(intros q Hq; specialize (PreH61 q ltac:(lia)); lia)) as [Hlo Hhi].
  specialize (PreH60 i_2 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure : solver_partial_solve_wit_24_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_5.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_6.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_7.
Qed.
