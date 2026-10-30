From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P042_1551C_interesting_story_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P042_1551C_interesting_story_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P042_1551C_interesting_story_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : 0 <= i < Zlength words_data) by lia.
  pose proof
    (letter_count_and_prefix_bounds__count_safety
       words_data i j cnt_data
       (Znth j (c_string (Znth i words_data nil)) 0 - 97)
       Hi (conj PreH1 PreH2) PreH24) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : 0 <= i < Zlength words_data) by lia.
  pose proof
    (letter_count_and_prefix_bounds__count_safety
       words_data i j cnt_data
       (Znth j (c_string (Znth i words_data nil)) 0 - 97)
       Hi (conj PreH1 PreH2) PreH24) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : 0 <= i < Zlength words_data) by lia.
  pose proof
    (letter_count_and_prefix_bounds__count_safety
       words_data i len cnt_data c
       Hi (conj PreH16 PreH5) PreH21) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : 0 <= i < Zlength words_data) by lia.
  pose proof
    (letter_count_and_prefix_bounds__count_safety
       words_data i len cnt_data c
       Hi (conj PreH16 PreH5) PreH21) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : 0 <= i < Zlength words_data) by lia.
  pose proof
    (letter_count_and_prefix_bounds__count_safety
       words_data i len cnt_data c
       Hi (conj PreH16 PreH5) PreH21) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : 0 <= i < Zlength words_data) by lia.
  pose proof
    (letter_count_and_prefix_bounds__count_safety
       words_data i len cnt_data c
       Hi (conj PreH16 PreH5) PreH21) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    assert (Hrange : 0 <= c * n_pre + take < 5 * n_pre) by lia;
    pose proof (PreH15 (c * n_pre + take) Hrange) as Hentry;
    lia).
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    assert (Hrange : 0 <= c * n_pre + take < 5 * n_pre) by lia;
    pose proof (PreH15 (c * n_pre + take) Hrange) as Hentry;
    lia).
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    assert (Hrange : 0 <= c * n_pre + take < 5 * n_pre) by lia;
    pose proof (PreH16 (c * n_pre + take) Hrange) as Hentry;
    lia).
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (score_mem := repeat (None : option Z) (Z.to_nat (5 * n_pre))).
  assert (Hscore_len : Zlength score_mem = 5 * n_pre).
  {
    unfold score_mem. rewrite Zlength_correct, repeat_length. lia.
  }
  assert (Hscore_state : ScoreBuildState words_data 0 score_mem).
  {
    unfold ScoreBuildState. split; [lia|].
    intros d k Hd Hk. split.
    - intros Hdone. lia.
    - intros _. unfold score_mem. rewrite Znth_repeat. reflexivity.
  }
  assert (Hchars : forall k q,
    (((0 <= k /\ k < n_pre) /\ 0 <= q) /\
      q < Zlength (Znth k words_data nil)) ->
    97 <= Znth q (Znth k words_data nil) 0 <= 101).
  {
    intros k q [[[Hk0 Hklt] Hq0] Hqlt].
    assert (Hword : Znth k words_data __default__List_Z =
      Znth k words_data nil).
    { apply Znth_indep. lia. }
    apply PreH5. rewrite Hword.
    repeat split; try assumption; lia.
  }
  Exists score_mem.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full retval (5 * n_pre)).
    unfold score_mem. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH8 i ltac:(lia)).
  destruct PreH8 as [[Hrows Hvalid] Hlen].
  assert (Hirows : 0 <= i < Zlength rows) by lia.
  rewrite (Znth_indep rows i __default__List_Z nil Hirows).
  rewrite Hrows.
  unfold string_length.
  assert (Hc_len : Zlength (c_string (Znth i words_data nil)) =
      Zlength (Znth i words_data nil) + 1).
  { unfold c_string.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia. }
  rewrite Hc_len.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply count_prefix_zero__char_prefix.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold string_length in PreH1.
  pose proof (Zlength_nonneg (Znth i words_data nil)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite c_string_Znth_inside by exact H.
  apply PreH6.
  unfold string_length in H.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_5 : solver_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH20 j ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH20 j ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply count_prefix_step__char_prefix.
  - lia.
  - lia.
  - rewrite <- c_string_Znth_inside by (unfold string_length; lia).
    lia.
  - exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace len with j by lia.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ScoreBuildState in PreH17.
  unfold ScoreRowState.
  destruct PreH17 as [Hlength Hstate].
  split.
  - exact Hlength.
  - intros d k Hd Hk.
    specialize (Hstate d k Hd Hk).
    destruct Hstate as [Hdone Hrest].
    split.
    + exact Hdone.
    + split.
      * intros [Hki Hdneg].
        lia.
      * intros Hcase.
        apply Hrest.
        destruct Hcase as [Hgt | [Heq Hnonneg]]; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_4 : solver_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH6.
  eapply score_row_store_step__score_row; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (c = 5) by lia. subst c.
  eapply score_row_complete__score_row; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_spatial : solver_entail_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 <= i < n_pre) by lia.
  specialize (PreH8 i Hi).
  destruct PreH8 as [[Hrow Hvalid] Hstrlen].
  pose proof (CharPtrArray2.missing_i_merge_to_full
    words_pre i n_pre row_ptr rows
      (c_string (Znth i words_data nil))) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (c_string (Znth i words_data nil)))
      (c_string (Znth i words_data nil))) with
    (CharArray.full row_ptr
      (Zlength (c_string (Znth i words_data nil)))
      (c_string (Znth i words_data nil))) in Hmerge.
  assert (Hcslen :
    Zlength (c_string (Znth i words_data nil)) = len + 1).
  {
    unfold c_string.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  }
  rewrite Hcslen in Hmerge.
  assert (Hreplace :
    replace_Znth i (c_string (Znth i words_data nil)) rows = rows).
  {
    rewrite <- Hrow.
    apply replace_Znth_Znth.
  }
  rewrite Hreplace in Hmerge.
  sep_apply_r_atomic Hmerge.
  all: try cancel; try lia; try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = Zlength words_data) by lia.
  subst i.
  destruct (score_build_materialize__score_table words_data score_mem
    ltac:(lia) PreH12) as [scores [Hmem Htable]].
  pose proof (proj1 Htable) as Hscores_len.
  Exists scores.
  split_pure_spatial.
  - rewrite Hmem.
    sep_apply_l_atomic
      (IntArray.mixed_full_to_full score (5 * n_pre) scores).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (n := Zlength words_data) in *.
  set (d := p / n).
  set (k := p mod n).
  assert (Hn : 0 < n) by lia.
  assert (Hk : 0 <= k < n).
  { subst k. apply Z.mod_pos_bound. lia. }
  assert (Hd0 : 0 <= d).
  { subst d. apply Z_div_pos; lia. }
  assert (Hp : d * n + k = p).
  { subst d k. pose proof (Z.div_mod p n ltac:(lia)). nia. }
  assert (Hd5 : d < 5) by nia.
  assert (Hentry : Znth p scores_2 0 =
    WordScore (97 + d) (Znth k words_data nil)).
  {
    rewrite <- Hp.
    apply score_table_entry__score_table; try assumption; lia.
  }
  rewrite Hentry.
  pose proof (word_score_abs_bound__score_table
    (97 + d) (Znth k words_data nil)) as Hscore.
  pose proof (word_length_le_total__score_table words_data k
    ltac:(lia)) as Hword.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold AnswerState.
  repeat split; try lia.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PreparedScoreTable.
  destruct PreH7 as [Hlen Hblocks].
  split; [exact Hlen|].
  intros d Hd. split.
  - intros Hlt. lia.
  - intros _. apply Hblocks. exact Hd.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (before := sublist 0 (c * n_pre) scores).
  set (block := sublist (c * n_pre) ((c + 1) * n_pre) scores).
  set (after := sublist ((c + 1) * n_pre) (5 * n_pre) scores).
  assert (Hscores : scores = before ++ block ++ after).
  { unfold before, block, after.
    rewrite <- (sublist_split (c * n_pre) (5 * n_pre)
      ((c + 1) * n_pre) scores) by nia.
    rewrite <- (sublist_split 0 (5 * n_pre) (c * n_pre) scores) by nia.
    symmetry. apply sublist_self. symmetry. exact PreH11. }
  assert (Hbefore : Zlength before = c * n_pre).
  { unfold before. rewrite Zlength_sublist by nia. lia. }
  assert (Hblock : Zlength block = n_pre).
  { unfold block. rewrite Zlength_sublist by nia. lia. }
  assert (Hafter : Zlength after = (5 - c - 1) * n_pre).
  { unfold after. rewrite Zlength_sublist by nia. lia. }
  assert (Hprefix :
    sublist 0 (c * n_pre) (before ++ block ++ after) = before).
  { rewrite <- Hbefore. apply sublist_app_exact1. }
  assert (Htail :
    sublist (c * n_pre) (5 * n_pre) (before ++ block ++ after) =
      block ++ after).
  { rewrite sublist_split_app_r with (len := c * n_pre) by nia.
    replace (c * n_pre - c * n_pre) with 0 by lia.
    replace (5 * n_pre - c * n_pre) with (Zlength (block ++ after))
      by (rewrite Zlength_app, Hblock, Hafter; nia).
    apply sublist_self. reflexivity. }
  assert (Hblock_sub : sublist 0 n_pre (block ++ after) = block).
  { rewrite <- Hblock. apply sublist_app_exact1. }
  assert (Hafter_sub :
    sublist n_pre (5 * n_pre - c * n_pre) (block ++ after) = after).
  { rewrite sublist_split_app_r with (len := n_pre) by nia.
    replace (n_pre - n_pre) with 0 by nia.
    replace (5 * n_pre - c * n_pre - n_pre) with (Zlength after)
      by nia.
    apply sublist_self. reflexivity. }
  Exists before block after.
  split_pure_spatial.
  - rewrite Hscores.
    sep_apply_l_atomic (IntArray.full_split_to_full score (c * n_pre)
      (5 * n_pre) (before ++ block ++ after) ltac:(nia)).
    rewrite Hprefix, Htail.
    sep_apply_l_atomic (IntArray.full_split_to_full
      (score + c * n_pre * sizeof(INT)) n_pre
      (5 * n_pre - c * n_pre) (block ++ after) ltac:(nia)).
    rewrite Hblock_sub, Hafter_sub.
    sep_apply_l_atomic (IntArray.full_to_seg score (c * n_pre) before).
    sep_apply_l_atomic (IntArray.full_to_seg
      (score + c * n_pre * sizeof(INT) + n_pre * sizeof(INT))
      (5 * n_pre - c * n_pre - n_pre) after).
    replace (score + c * n_pre * sizeof(INT) + n_pre * sizeof(INT))
      with (score + ((c + 1) * n_pre) * sizeof(INT)) by lia.
    replace (5 * n_pre - c * n_pre - n_pre)
      with (5 * n_pre - (c + 1) * n_pre) by lia.
    rewrite <- (IntArray.seg_shift score ((c + 1) * n_pre) 0
      (5 * n_pre - (c + 1) * n_pre) after).
    replace ((c + 1) * n_pre + 0) with ((c + 1) * n_pre) by lia.
    replace ((c + 1) * n_pre + (5 * n_pre - (c + 1) * n_pre))
      with (5 * n_pre) by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    + rewrite <- Hscores. exact PreH12.
    + intros p Hp. unfold block.
      rewrite Znth_sublist by nia.
      apply PreH14. nia.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (scores := before ++ sorted ++ after).
  assert (Hscores_length : Zlength scores = 5 * n_pre).
  { unfold scores. repeat rewrite Zlength_app. nia. }
  pose proof (prepared_table_replace_block__block_sorting
    words_data c n_pre before block sorted after
    PreH4 ltac:(lia) PreH15 PreH16 PreH3 PreH17
    PreH13 PreH1 PreH2) as Hreplace.
  destruct Hreplace as [Hprepared Hmiddle].
  assert (Hbounds : forall p, 0 <= p < 5 * n_pre ->
      -200000 <= Znth p scores 0 <= 200000).
  { intros p Hp.
    apply (prepared_table_pointwise_bounds__block_sorting
      words_data (c + 1) scores); try nia; try exact PreH7;
      try exact Hprepared. }
  Exists scores.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_seg
      (score + c * n_pre * sizeof(INT)) n_pre sorted).
    rewrite <- (IntArray.seg_shift score (c * n_pre) 0 n_pre sorted).
    replace (c * n_pre + 0) with (c * n_pre) by nia.
    replace (c * n_pre + n_pre) with ((c + 1) * n_pre) by nia.
    sep_apply_l_atomic (IntArray.seg_merge_to_seg score 0 (c * n_pre)
      ((c + 1) * n_pre) before sorted ltac:(nia)).
    sep_apply_l_atomic (IntArray.seg_merge_to_full score 0
      ((c + 1) * n_pre) (5 * n_pre) (before ++ sorted) after
      ltac:(nia)).
    replace (score + 0 * sizeof(INT)) with score by nia.
    replace (5 * n_pre - 0) with (5 * n_pre) by nia.
    unfold scores. rewrite app_assoc.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    + unfold scores. rewrite Hmiddle. exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply positive_prefix_zero__positive_prefix.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_3 : solver_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH14.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hscore :
    Znth take (sublist (c * n_pre) ((c + 1) * n_pre) scores_2) 0 =
    Znth (c * n_pre + take) scores_2 0).
  {
    rewrite Znth_sublist by lia.
    f_equal.
    ring.
  }
  rewrite <- Hscore.
  rewrite <- Hscore in PreH1.
  eapply positive_prefix_step__positive_prefix.
  - exact PreH23.
  - assert (Hblocklength :
      Zlength (sublist (c * n_pre) ((c + 1) * n_pre) scores_2) = n_pre).
    {
      rewrite Zlength_sublist by nia.
      nia.
    }
    rewrite Hblocklength.
    lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hblocklength :
    Zlength (sublist (c * n_pre) ((c + 1) * n_pre) scores_2) = n_pre).
  {
    rewrite Zlength_sublist by nia.
    nia.
  }
  assert (Htakeblock :
    0 <= take <
      Zlength (sublist (c * n_pre) ((c + 1) * n_pre) scores_2)) by lia.
  assert (Hscore :
    Znth take (sublist (c * n_pre) ((c + 1) * n_pre) scores_2) 0 =
    Znth (c * n_pre + take) scores_2 0).
  {
    rewrite Znth_sublist by lia.
    f_equal.
    ring.
  }
  assert (Hnewsum :
    sum + Znth (c * n_pre + take) scores_2 0 =
    fold_right Z.add 0
      (sublist 0 (take + 1)
        (sublist (c * n_pre) ((c + 1) * n_pre) scores_2))).
  {
    rewrite sum_sublist_snoc__positive_prefix by exact Htakeblock.
    destruct PreH23 as [_ [Hacc _]].
    rewrite <- Hacc.
    rewrite Hscore.
    reflexivity.
  }
  rewrite Hnewsum.
  eapply Z.le_trans.
  - eapply positive_word_scores_sum_bound__positive_prefix.
    + unfold PreparedScoreTable in PreH13.
      destruct PreH13 as [_ Hprepared].
      specialize (Hprepared c ltac:(lia)).
      cbv zeta in Hprepared.
      destruct Hprepared as [Hprocessed _].
      specialize (Hprocessed ltac:(lia)).
      rewrite <- PreH3 in Hprocessed.
      exact (proj1 Hprocessed).
    + rewrite Hblocklength.
      lia.
  - exact PreH6.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_3 : solver_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_16_1_split_goal_1 : solver_entail_wit_16_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply decreasing_positive_prefix_is_letter_best__letter_optimality
    with (block := sublist (c * n_pre) ((c + 1) * n_pre) scores_2)
         (acc := sum).
  - unfold PreparedScoreTable in PreH12. destruct PreH12 as [_ Htable].
    specialize (Htable c ltac:(lia)). cbn in Htable.
    destruct Htable as [Hprocessed _]. specialize (Hprocessed ltac:(lia)).
    rewrite <- PreH2 in Hprocessed.
    exact (proj1 Hprocessed).
  - exact PreH14.
  - exact PreH22.
  - left. destruct PreH22 as [[_ Htakeblock] _].
    assert (Hblocklen :
      Zlength (sublist (c * n_pre) ((c + 1) * n_pre) scores_2) = n_pre).
    { unfold PreparedScoreTable in PreH12. destruct PreH12 as [_ Htable].
      specialize (Htable c ltac:(lia)). cbn in Htable.
      destruct Htable as [Hprocessed _]. specialize (Hprocessed ltac:(lia)).
      rewrite <- PreH2 in Hprocessed.
      pose proof (Permutation_length (proj1 Hprocessed)) as Hplen.
      rewrite Zlength_correct, <- Hplen. unfold ScoreBlock.
      rewrite length_map, <- Zlength_correct, <- PreH2. reflexivity. }
    lia.
Qed.

Lemma proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_2_split_goal_1 : solver_entail_wit_16_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply decreasing_positive_prefix_is_letter_best__letter_optimality
    with (block := sublist (c * n_pre) ((c + 1) * n_pre) scores_2)
         (acc := sum).
  - unfold PreparedScoreTable in PreH13. destruct PreH13 as [_ Htable].
    specialize (Htable c ltac:(lia)). cbn in Htable.
    destruct Htable as [Hprocessed _]. specialize (Hprocessed ltac:(lia)).
    rewrite <- PreH3 in Hprocessed.
    exact (proj1 Hprocessed).
  - exact PreH15.
  - exact PreH23.
  - right. split.
    + assert (Hblocklen :
        Zlength (sublist (c * n_pre) ((c + 1) * n_pre) scores_2) = n_pre).
      { unfold PreparedScoreTable in PreH13. destruct PreH13 as [_ Htable].
        specialize (Htable c ltac:(lia)). cbn in Htable.
        destruct Htable as [Hprocessed _]. specialize (Hprocessed ltac:(lia)).
        rewrite <- PreH3 in Hprocessed.
        pose proof (Permutation_length (proj1 Hprocessed)) as Hplen.
        rewrite Zlength_correct, <- Hplen. unfold ScoreBlock.
        rewrite length_map, <- Zlength_correct, <- PreH3. reflexivity. }
      lia.
    + rewrite Znth_sublist by lia.
      replace (take + c * n_pre) with (c * n_pre + take) by lia.
      exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_17_1_split_goal_1 : solver_entail_wit_17_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  eapply prepared_score_entry_bounds__answer_transition; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_1_split_goal_2 : solver_entail_wit_17_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace take with (Z.max answer take) by (apply Z.max_r; lia).
  eapply answer_state_step__answer_transition; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_1 : solver_entail_wit_17_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_17_2_split_goal_1 : solver_entail_wit_17_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  eapply prepared_score_entry_bounds__answer_transition; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_2_split_goal_2 : solver_entail_wit_17_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace answer with (Z.max answer take) by (apply Z.max_l; lia).
  eapply answer_state_step__answer_transition; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_2 : solver_entail_wit_17_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (c = 5) by lia.
  subst c.
  apply answer_state_five_implies_spec__final_result.
  exact PreH13.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH11 as [[Hrow Hvalid] Hlen].
  dump_pre_spatial.
  exact Hvalid.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH11 as [[Hrow Hvalid] Hlen].
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_2.
Qed.
