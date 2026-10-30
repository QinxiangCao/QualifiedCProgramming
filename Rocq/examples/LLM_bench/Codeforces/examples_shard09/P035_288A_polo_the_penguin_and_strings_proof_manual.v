From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P035_288A_polo_the_penguin_and_strings_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P035_288A_polo_the_penguin_and_strings_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P035_288A_polo_the_penguin_and_strings_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos i 2 ltac:(lia) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos i 2 ltac:(lia) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst n_pre. subst k_pre.
  assert (length = 1) by lia. subst length.
  unfold PoloCandidate.
  destruct (Z.eq_dec 1 1) as [_ | Hneq]; [|contradiction].
  unfold Spec.
  right. exists (cons 97 (@nil Z)).
  split; [reflexivity |].
  split.
  - unfold PoloString.
    split.
    + reflexivity.
    + split.
      * constructor; [lia | constructor].
      * split.
        -- apply set_card_unique__alternating_prefix with (x := 97).
           ++ split; [lia | simpl; auto].
           ++ intros y [_ Hy]. simpl in Hy. destruct Hy as [Hy | []]. congruence.
        -- intros j Hj. lia.
  - intros q Hq.
    destruct Hq as [Hqlen [Halpha [Hcard Hadj]]].
    destruct q as [|a q].
    + rewrite Zlength_nil in Hqlen. lia.
    + destruct q as [|b q].
      * inversion Halpha as [|? ? Ha _]; subst.
        unfold LexLE.
        destruct (Z.eq_dec a 97) as [-> | Hne].
        -- left. reflexivity.
        -- right. left. exists 0.
           split; [rewrite !Zlength_cons, !Zlength_nil; simpl; lia |].
           split.
           ++ intros j Hj. lia.
           ++ rewrite !Znth0_cons. lia.
      * rewrite !Zlength_cons in Hqlen.
        pose proof (Zlength_nonneg q). lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre. subst k_pre.
  assert (length = 1) by lia. subst length.
  unfold PoloCandidate.
  destruct (Z.eq_dec 1 1) as [_ | Hneq]; [|contradiction].
  unfold CharArray.full, store_array.
  simpl.
  cancel.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hremmod : i % 2 = i mod 2).
  { rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Hremmod.
  rewrite signed_last_nbits_eq by
      (pose proof (Z.mod_pos_bound i 2 ltac:(lia)); lia).
  apply alternating_prefix_snoc__alternating_prefix.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with alt by lia.
  replace (alt + 0) with alt by lia.
  replace (IncreasingTail 0) with (@nil Z) by
      (unfold IncreasingTail; reflexivity).
  rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- app_assoc.
  rewrite increasing_tail_snoc__candidate_completion by lia.
  replace (alt + (i + 1)) with ((alt + i) + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply polo_candidate_spec_multi__candidate_completion; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_spatial : solver_entail_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = k_pre - 2) by lia.
  subst i.
  rewrite polo_candidate_unfold_multi__candidate_completion by lia.
  replace (n_pre - (k_pre - 2)) with alt by lia.
  replace (alt + (k_pre - 2) + 1) with (n_pre + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH9 as Hspec.
  assert (Hlen : Zlength (PoloCandidate n_pre k_pre) = n_pre).
  {
    unfold Spec in Hspec.
    destruct Hspec as [[Hnone _] | [s [Hsome [Hpolo _]]]].
    - discriminate.
    - injection Hsome as Heq. subst s.
      exact (proj1 Hpolo).
  }
  subst length alphabet_size.
  Exists (PoloCandidate n_pre k_pre) (Some (PoloCandidate n_pre k_pre)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. unfold P035ReturnBridge. right. eauto.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH5 as Hspec.
  assert (Hlen : Zlength (PoloCandidate n_pre k_pre) = n_pre).
  {
    unfold Spec in Hspec.
    destruct Hspec as [[Hnone _] | [s [Hsome [Hpolo _]]]].
    - discriminate.
    - injection Hsome as Heq. subst s.
      exact (proj1 Hpolo).
  }
  subst n_pre k_pre length alphabet_size.
  Exists (PoloCandidate 1 1) (Some (PoloCandidate 1 1)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. unfold P035ReturnBridge. right. eauto.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold P035ReturnBridge.
  left.
  split; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_2 : solver_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  left.
  split; [reflexivity |].
  intros (s & Hs).
  unfold PoloString in Hs.
  destruct Hs as (Hlen & _ & Hcard & _).
  pose proof (polostring_symbol_count_le_length__impossible_returns s).
  lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold P035ReturnBridge.
  left.
  split; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_2 : solver_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  left.
  split; [reflexivity |].
  intros (s & Hs).
  assert (Hn : n_pre = length) by lia.
  assert (Ha : alphabet_size = 1) by lia.
  rewrite <- Hn, Ha in Hs.
  pose proof (polostring_one_symbol_length_le_one__impossible_returns n_pre s Hs).
  lia.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_2.
Qed.
