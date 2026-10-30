From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P039_1955D_inaccurate_subsequence_search_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P039_1955D_inaccurate_subsequence_search_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P039_1955D_inaccurate_subsequence_search_lib.
Local Open Scope sac.

Lemma proof_of_minimum_return_wit_1_split_goal_1 : minimum_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold z_min; rewrite Z.min_l by lia; reflexivity).
Qed.

Lemma proof_of_minimum_return_wit_1 : minimum_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimum_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_minimum_return_wit_2_split_goal_1 : minimum_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold z_min; rewrite Z.min_r by lia; reflexivity).
Qed.

Lemma proof_of_minimum_return_wit_2 : minimum_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimum_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_2_split_goal_1 : solver_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  pose proof (frequency_table_entry_bounds__initial_safety
    (sublist 0 i b_data) need_data (Znth i b_data 0)
    PreH12 ltac:(lia)) as Hfrequency.
  assert (Hprefix_length : Zlength (sublist 0 i b_data) = i).
  { rewrite Zlength_sublist; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_2_split_goal_2 : solver_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  pose proof (frequency_table_entry_bounds__initial_safety
    (sublist 0 i b_data) need_data (Znth i b_data 0)
    PreH12 ltac:(lia)) as Hfrequency.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    pose proof (PreH7 i ltac:(lia)) as Hvalue.
    pose proof (frequency_table_entry_bounds__initial_safety
      (sublist 0 i b_data) need_data (Znth i b_data 0)
      PreH12 ltac:(lia)) as Hfrequency.
    assert (Hprefix_length : Zlength (sublist 0 i b_data) = i).
    { rewrite Zlength_sublist; lia. }
    lia.
  - dump_pre_spatial.
    pose proof (PreH7 i ltac:(lia)) as Hvalue.
    pose proof (frequency_table_entry_bounds__initial_safety
      (sublist 0 i b_data) need_data (Znth i b_data 0)
      PreH12 ltac:(lia)) as Hfrequency.
    lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  pose proof (frequency_table_entry_bounds__initial_safety
    (sublist 0 i values) have_data (Znth i values 0)
    PreH17 ltac:(lia)) as Hhave.
  pose proof (frequency_table_entry_bounds__initial_safety
    b_data need_data (Znth i values 0) PreH16 ltac:(lia)) as Hneed.
  assert (Hprefix_length : Zlength (sublist 0 i values) = i).
  { rewrite Zlength_sublist; lia. }
  unfold z_min in PreH1.
  destruct (Z_le_dec (Znth (Znth i values 0) have_data 0)
    (Znth (Znth i values 0) need_data 0)).
  - rewrite Z.min_l in PreH1 by lia. lia.
  - rewrite Z.min_r in PreH1 by lia. lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  pose proof (frequency_table_entry_bounds__initial_safety
    (sublist 0 i values) have_data (Znth i values 0)
    PreH17 ltac:(lia)) as Hhave.
  pose proof (frequency_table_entry_bounds__initial_safety
    b_data need_data (Znth i values 0) PreH16 ltac:(lia)) as Hneed.
  assert (Hprefix_length : Zlength (sublist 0 i values) = i).
  { rewrite Zlength_sublist; lia. }
  unfold z_min in PreH1.
  destruct (Z_le_dec (Znth (Znth i values 0) have_data 0)
    (Znth (Znth i values 0) need_data 0)).
  - rewrite Z.min_l in PreH1 by lia. lia.
  - rewrite Z.min_r in PreH1 by lia. lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_8_split_goal_1 : solver_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  pose proof (frequency_table_entry_bounds__initial_safety
    (sublist 0 i values) have_data (Znth i values 0)
    PreH17 ltac:(lia)) as Hhave.
  assert (Hprefix_length : Zlength (sublist 0 i values) = i).
  { rewrite Zlength_sublist; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_8_split_goal_2 : solver_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  pose proof (frequency_table_entry_bounds__initial_safety
    (sublist 0 i values) have_data (Znth i values 0)
    PreH17 ltac:(lia)) as Hhave.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_9_split_goal_1 : solver_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH8 i ltac:(lia)) as Hvalue.
  unfold FrequencyTable in PreH18.
  destruct PreH18 as [Hhave_length _].
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  unfold z_min in PreH1, PreH2.
  pose proof (z_min_increment_bounds__initial_safety
    (Znth (Znth i values 0) have_data 0)
    (Znth (Znth i values 0) need_data 0)) as Hincrement.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_9_split_goal_2 : solver_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH8 i ltac:(lia)) as Hvalue.
  unfold FrequencyTable in PreH18.
  destruct PreH18 as [Hhave_length _].
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  unfold z_min in PreH1, PreH2.
  pose proof (z_min_increment_bounds__initial_safety
    (Znth (Znth i values 0) have_data 0)
    (Znth (Znth i values 0) need_data 0)) as Hincrement.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 (i - m_pre) ltac:(lia)) as Hv.
  assert (Hvrange :
    0 <= Znth (i - m_pre) values 0 < 1000001) by lia.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ _ PreH18 Hvrange) as Hhave.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ _ PreH17 Hvrange) as Hneed.
  rewrite Zlength_sublist in Hhave by lia.
  unfold z_min in PreH1.
  destruct (Z_le_dec
    (Znth (Znth (i - m_pre) values 0) have_data 0)
    (Znth (Znth (i - m_pre) values 0) need_data 0)).
  - rewrite Z.min_l in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_r in PreH1 by lia.
    dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 (i - m_pre) ltac:(lia)) as Hv.
  assert (Hvrange :
    0 <= Znth (i - m_pre) values 0 < 1000001) by lia.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ _ PreH18 Hvrange) as Hhave.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ _ PreH17 Hvrange) as Hneed.
  rewrite Zlength_sublist in Hhave by lia.
  unfold z_min in PreH1.
  destruct (Z_le_dec
    (Znth (Znth (i - m_pre) values 0) have_data 0)
    (Znth (Znth (i - m_pre) values 0) need_data 0)).
  - rewrite Z.min_l in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_r in PreH1 by lia.
    dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 (i - m_pre) ltac:(lia)) as Hv.
  assert (Hvrange :
    0 <= Znth (i - m_pre) values 0 < 1000001) by lia.
  assert (Hwinlen :
    Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hfirst :
    Znth 0 (sublist (i - m_pre) i values) 0 =
    Znth (i - m_pre) values 0).
  { rewrite Znth_sublist by lia. reflexivity. }
  assert (Hfirst_index :
    0 <= 0 < Zlength (sublist (i - m_pre) i values)).
  { rewrite Hwinlen. lia. }
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ _ PreH18 Hvrange) as Hhave.
  pose proof (frequency_table_present__sliding_remove_safety
    _ _ _ 0 PreH18 Hvrange Hfirst_index Hfirst) as Hpresent.
  rewrite Hwinlen in Hhave.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 (i - m_pre) ltac:(lia)) as Hv.
  assert (Hvrange :
    0 <= Znth (i - m_pre) values 0 < 1000001) by lia.
  assert (Hwinlen :
    Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hfirst :
    Znth 0 (sublist (i - m_pre) i values) 0 =
    Znth (i - m_pre) values 0).
  { rewrite Znth_sublist by lia. reflexivity. }
  assert (Hfirst_index :
    0 <= 0 < Zlength (sublist (i - m_pre) i values)).
  { rewrite Hwinlen. lia. }
  pose proof (frequency_table_present__sliding_remove_safety
    _ _ _ 0 PreH18 Hvrange Hfirst_index Hfirst) as Hpresent.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_15_split_goal_1 : solver_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH8 (i - m_pre) ltac:(lia)) as Hv.
  set (v := Znth (i - m_pre) values 0) in *.
  assert (Hvrange : 0 <= v < 1000001) by lia.
  assert (Hwinlen :
    Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hfirst : Znth 0 (sublist (i - m_pre) i values) 0 = v).
  { unfold v. rewrite Znth_sublist by lia. reflexivity. }
  assert (Hfirst_index :
    0 <= 0 < Zlength (sublist (i - m_pre) i values)).
  { rewrite Hwinlen. lia. }
  pose proof (frequency_table_present__sliding_remove_safety
    _ _ v 0 PreH19 Hvrange Hfirst_index Hfirst) as Hpresent.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ v PreH19 Hvrange) as Hhave.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ v PreH18 Hvrange) as Hneed.
  destruct PreH19 as [Hhave_len _].
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  set (h := Znth v have_data 0) in *.
  set (n := Znth v need_data 0) in *.
  unfold z_min in PreH1, PreH2.
  destruct (Z_le_dec h n) as [Hhn | Hhn];
    destruct (Z_le_dec (h - 1) n) as [Hdec | Hdec].
  - rewrite Z.min_l in PreH2 by lia.
    rewrite Z.min_l in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_l in PreH2 by lia.
    rewrite Z.min_r in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_r in PreH2 by lia.
    rewrite Z.min_l in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_r in PreH2 by lia.
    rewrite Z.min_r in PreH1 by lia.
    dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_15_split_goal_2 : solver_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH8 (i - m_pre) ltac:(lia)) as Hv.
  set (v := Znth (i - m_pre) values 0) in *.
  assert (Hvrange : 0 <= v < 1000001) by lia.
  assert (Hwinlen :
    Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hfirst : Znth 0 (sublist (i - m_pre) i values) 0 = v).
  { unfold v. rewrite Znth_sublist by lia. reflexivity. }
  assert (Hfirst_index :
    0 <= 0 < Zlength (sublist (i - m_pre) i values)).
  { rewrite Hwinlen. lia. }
  pose proof (frequency_table_present__sliding_remove_safety
    _ _ v 0 PreH19 Hvrange Hfirst_index Hfirst) as Hpresent.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ v PreH19 Hvrange) as Hhave.
  pose proof (frequency_table_entry_bounds__sliding_remove_safety
    _ _ v PreH18 Hvrange) as Hneed.
  destruct PreH19 as [Hhave_len _].
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  set (h := Znth v have_data 0) in *.
  set (n := Znth v need_data 0) in *.
  unfold z_min in PreH1, PreH2.
  destruct (Z_le_dec h n) as [Hhn | Hhn];
    destruct (Z_le_dec (h - 1) n) as [Hdec | Hdec].
  - rewrite Z.min_l in PreH2 by lia.
    rewrite Z.min_l in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_l in PreH2 by lia.
    rewrite Z.min_r in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_r in PreH2 by lia.
    rewrite Z.min_l in PreH1 by lia.
    dump_pre_spatial. lia.
  - rewrite Z.min_r in PreH2 by lia.
    rewrite Z.min_r in PreH1 by lia.
    dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH9 (i - m_pre) ltac:(lia)) as Hx.
  pose proof (PreH9 i ltac:(lia)) as Hy.
  assert (Hwindow_len : Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth (i - m_pre) values 0) PreH19 ltac:(lia)) as Hneed_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth i values 0) PreH19 ltac:(lia)) as Hneed_y.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth (i - m_pre) values 0) PreH20 ltac:(lia)) as Hhave_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth i values 0) PreH20 ltac:(lia)) as Hhave_y.
  rewrite <- PreH12 in Hneed_x, Hneed_y.
  rewrite Hwindow_len in Hhave_x, Hhave_y.
  pose proof (proj1 PreH20) as Hhave_len.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth (i - m_pre) values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_x) as Hpost_x.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth i values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_y) as Hpost_y.
  assert (Hretval : 0 <= retval <= m_pre).
  { rewrite PreH3. apply z_min_bounds__sliding_add_safety; assumption. }
  assert (Hretval2 : -1 <= retval_2 <= m_pre).
  { rewrite PreH2. apply z_min_bounds__sliding_add_safety; [exact Hpost_x | lia]. }
  assert (Hretval3 : -1 <= retval_3 <= m_pre).
  { rewrite PreH1. apply z_min_bounds__sliding_add_safety; [exact Hpost_y | lia]. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH9 (i - m_pre) ltac:(lia)) as Hx.
  pose proof (PreH9 i ltac:(lia)) as Hy.
  assert (Hwindow_len : Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth (i - m_pre) values 0) PreH19 ltac:(lia)) as Hneed_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth i values 0) PreH19 ltac:(lia)) as Hneed_y.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth (i - m_pre) values 0) PreH20 ltac:(lia)) as Hhave_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth i values 0) PreH20 ltac:(lia)) as Hhave_y.
  rewrite <- PreH12 in Hneed_x, Hneed_y.
  rewrite Hwindow_len in Hhave_x, Hhave_y.
  pose proof (proj1 PreH20) as Hhave_len.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth (i - m_pre) values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_x) as Hpost_x.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth i values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_y) as Hpost_y.
  assert (Hretval : 0 <= retval <= m_pre).
  { rewrite PreH3. apply z_min_bounds__sliding_add_safety; assumption. }
  assert (Hretval2 : -1 <= retval_2 <= m_pre).
  { rewrite PreH2. apply z_min_bounds__sliding_add_safety; [exact Hpost_x | lia]. }
  assert (Hretval3 : -1 <= retval_3 <= m_pre).
  { rewrite PreH1. apply z_min_bounds__sliding_add_safety; [exact Hpost_y | lia]. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH9 i ltac:(lia)) as Hy.
  pose proof (PreH9 (i - m_pre) ltac:(lia)) as Hx.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data (Znth i values 0)
    PreH20 ltac:(lia)) as Hhave_y.
  assert (Hwindow_len : Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  rewrite Hwindow_len in Hhave_y.
  pose proof (proj1 PreH20) as Hhave_len.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth i values 0) m_pre
    Hhave_len ltac:(lia) ltac:(lia) Hhave_y) as Hpost_y.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH9 i ltac:(lia)) as Hy.
  pose proof (PreH9 (i - m_pre) ltac:(lia)) as Hx.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data (Znth i values 0)
    PreH20 ltac:(lia)) as Hhave_y.
  assert (Hwindow_len : Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  rewrite Hwindow_len in Hhave_y.
  pose proof (proj1 PreH20) as Hhave_len.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth i values 0) m_pre
    Hhave_len ltac:(lia) ltac:(lia) Hhave_y) as Hpost_y.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH10 (i - m_pre) ltac:(lia)) as Hx.
  pose proof (PreH10 i ltac:(lia)) as Hy.
  assert (Hwindow_len : Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth (i - m_pre) values 0) PreH20 ltac:(lia)) as Hneed_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth i values 0) PreH20 ltac:(lia)) as Hneed_y.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth (i - m_pre) values 0) PreH21 ltac:(lia)) as Hhave_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth i values 0) PreH21 ltac:(lia)) as Hhave_y.
  rewrite <- PreH13 in Hneed_x, Hneed_y.
  rewrite Hwindow_len in Hhave_x, Hhave_y.
  pose proof (proj1 PreH21) as Hhave_len.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth (i - m_pre) values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_x) as Hpost_x.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth i values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_y) as Hpost_y.
  assert (Hretval : 0 <= retval <= m_pre).
  { rewrite PreH4. apply z_min_bounds__sliding_add_safety; assumption. }
  assert (Hretval2 : -1 <= retval_2 <= m_pre).
  { rewrite PreH3. apply z_min_bounds__sliding_add_safety; [exact Hpost_x | lia]. }
  assert (Hretval3 : -1 <= retval_3 <= m_pre).
  { rewrite PreH2. apply z_min_bounds__sliding_add_safety; [exact Hpost_y | lia]. }
  assert (Hincremented :
    Znth (Znth i values 0)
      (replace_Znth (Znth i values 0)
        (Znth (Znth i values 0)
          (replace_Znth (Znth (i - m_pre) values 0)
            (Znth (Znth (i - m_pre) values 0) have_data 0 - 1) have_data) 0 + 1)
        (replace_Znth (Znth (i - m_pre) values 0)
          (Znth (Znth (i - m_pre) values 0) have_data 0 - 1) have_data)) 0 =
    Znth (Znth i values 0)
      (replace_Znth (Znth (i - m_pre) values 0)
        (Znth (Znth (i - m_pre) values 0) have_data 0 - 1) have_data) 0 + 1).
  { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth. lia. }
  assert (Hretval4 : 0 <= retval_4 <= m_pre + 1).
  { rewrite PreH1, Hincremented.
    apply z_min_bounds__sliding_add_safety; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH10 (i - m_pre) ltac:(lia)) as Hx.
  pose proof (PreH10 i ltac:(lia)) as Hy.
  assert (Hwindow_len : Zlength (sublist (i - m_pre) i values) = m_pre).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth (i - m_pre) values 0) PreH20 ltac:(lia)) as Hneed_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    b_data need_data (Znth i values 0) PreH20 ltac:(lia)) as Hneed_y.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth (i - m_pre) values 0) PreH21 ltac:(lia)) as Hhave_x.
  pose proof (frequency_table_entry_bounds__sliding_add_safety
    (sublist (i - m_pre) i values) have_data
    (Znth i values 0) PreH21 ltac:(lia)) as Hhave_y.
  rewrite <- PreH13 in Hneed_x, Hneed_y.
  rewrite Hwindow_len in Hhave_x, Hhave_y.
  pose proof (proj1 PreH21) as Hhave_len.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth (i - m_pre) values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_x) as Hpost_x.
  pose proof (replace_decrement_lookup_bounds__sliding_add_safety
    have_data (Znth (i - m_pre) values 0) (Znth i values 0)
    m_pre Hhave_len ltac:(lia) ltac:(lia) Hhave_y) as Hpost_y.
  assert (Hretval : 0 <= retval <= m_pre).
  { rewrite PreH4. apply z_min_bounds__sliding_add_safety; assumption. }
  assert (Hretval2 : -1 <= retval_2 <= m_pre).
  { rewrite PreH3. apply z_min_bounds__sliding_add_safety; [exact Hpost_x | lia]. }
  assert (Hretval3 : -1 <= retval_3 <= m_pre).
  { rewrite PreH2. apply z_min_bounds__sliding_add_safety; [exact Hpost_y | lia]. }
  assert (Hincremented :
    Znth (Znth i values 0)
      (replace_Znth (Znth i values 0)
        (Znth (Znth i values 0)
          (replace_Znth (Znth (i - m_pre) values 0)
            (Znth (Znth (i - m_pre) values 0) have_data 0 - 1) have_data) 0 + 1)
        (replace_Znth (Znth (i - m_pre) values 0)
          (Znth (Znth (i - m_pre) values 0) have_data 0 - 1) have_data)) 0 =
    Znth (Znth i values 0)
      (replace_Znth (Znth (i - m_pre) values 0)
        (Znth (Znth (i - m_pre) values 0) have_data 0 - 1) have_data) 0 + 1).
  { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth. lia. }
  assert (Hretval4 : 0 <= retval_4 <= m_pre + 1).
  { rewrite PreH1, Hincremented.
    apply z_min_bounds__sliding_add_safety; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  apply frequency_table_empty__table_initialization.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  apply PreH5.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply frequency_table_prefix_step__table_initialization.
  - lia.
  - specialize (PreH7 i).
    lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  apply table_match_score_zero__table_initialization with (xs := b_data).
  assert (Hi : i = m_pre) by lia.
  subst i.
  rewrite PreH9 in PreH12.
  rewrite sublist_self in PreH12 by reflexivity.
  exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  apply frequency_table_empty__table_initialization.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = m_pre) by lia.
  subst i.
  rewrite PreH9 in PreH12.
  rewrite sublist_self in PreH12 by reflexivity.
  exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  apply PreH7.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_5 : solver_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  apply PreH6.
  lia.
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
  destruct PreH18 as [Hlen Hfreq].
  assert (Hidx : 0 <= Znth i values 0 < 1000001).
  { specialize (PreH8 i ltac:(lia)). lia. }
  pose proof (table_match_score_update__window_semantics need_data_2
    have_data_2 (Znth i values 0)
    (Znth (Znth i values 0) have_data_2 0 + 1) matched
    Hlen Hidx PreH19) as Hscore.
  unfold z_min in PreH1, PreH2.
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  rewrite <- PreH2, <- PreH1 in Hscore. exact Hscore.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply frequency_table_push__window_semantics.
  - lia.
  - specialize (PreH8 i ltac:(lia)). lia.
  - exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proof_of_solver_entail_wit_4_split_goal_1 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as Hscore.
  pose proof (proof_of_solver_entail_wit_4_split_goal_2 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as Hfreq.
  assert (Hb : Forall (fun x => 0 <= x < 1000001) b_data).
  { apply Forall_Znth_intro__window_semantics. intros j Hj.
    specialize (PreH9 j Hj). lia. }
  assert (Hw : Forall (fun x => 0 <= x < 1000001)
    (sublist 0 (i + 1) values)).
  { apply Forall_Znth_intro__window_semantics.
    eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH8 j Hj). lia. }
  pose proof (table_match_score_bounds__window_semantics b_data
    (sublist 0 (i + 1) values) need_data_2
    (replace_Znth (Znth i values 0)
      (Znth (Znth i values 0) have_data_2 0 + 1) have_data_2)
    (matched - retval + retval_2) Hb Hw PreH17 Hfreq Hscore) as Hbounds.
  rewrite Zlength_sublist in Hbounds by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proof_of_solver_entail_wit_4_split_goal_1 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as Hscore.
  pose proof (proof_of_solver_entail_wit_4_split_goal_2 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as Hfreq.
  assert (Hb : Forall (fun x => 0 <= x < 1000001) b_data).
  { apply Forall_Znth_intro__window_semantics. intros j Hj.
    specialize (PreH9 j Hj). lia. }
  assert (Hw : Forall (fun x => 0 <= x < 1000001)
    (sublist 0 (i + 1) values)).
  { apply Forall_Znth_intro__window_semantics.
    eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH8 j Hj). lia. }
  pose proof (table_match_score_bounds__window_semantics b_data
    (sublist 0 (i + 1) values) need_data_2
    (replace_Znth (Znth i values 0)
      (Znth (Znth i values 0) have_data_2 0 + 1) have_data_2)
    (matched - retval + retval_2) Hb Hw PreH17 Hfreq Hscore) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = m_pre) by lia. subst i.
  assert (Hblen : Zlength b_data = Zlength (sublist 0 m_pre values)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hbnd : forall j, 0 <= j < Zlength b_data ->
    0 <= Znth j b_data 0 < 1000001).
  { intros j Hj. specialize (PreH8 j Hj). lia. }
  assert (Hwbnd : forall j, 0 <= j < Zlength (sublist 0 m_pre values) ->
    0 <= Znth j (sublist 0 m_pre values) 0 < 1000001).
  { eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH7 j Hj). lia. }
  assert (Hgood : GoodWindow b_data (sublist 0 m_pre values) k_pre).
  { apply (proj2 (good_window_iff_match_score__window_semantics
      b_data (sublist 0 m_pre values) need_data_2 have_data_2 matched k_pre
      Hblen Hbnd Hwbnd PreH16 PreH17 PreH18)). exact PreH1. }
  destruct (counted_good_windows_step__window_semantics k_pre values b_data
    0 0 ltac:(lia) (counted_good_windows_zero__window_semantics
      k_pre values b_data)) as [Hstep _].
  replace (0 + Zlength b_data) with m_pre in Hstep by lia.
  replace (m_pre - m_pre + 1) with (0 + 1) by lia.
  exact (Hstep Hgood).
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with m_pre in PreH17 by lia.
  replace (m_pre - m_pre) with 0 by lia. exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto). apply PreH8; assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_4 : solver_entail_wit_5_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto). apply PreH7; assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = m_pre) by lia. subst i.
  assert (Hblen : Zlength b_data = Zlength (sublist 0 m_pre values)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hbnd : forall j, 0 <= j < Zlength b_data ->
    0 <= Znth j b_data 0 < 1000001).
  { intros j Hj. specialize (PreH8 j Hj). lia. }
  assert (Hwbnd : forall j, 0 <= j < Zlength (sublist 0 m_pre values) ->
    0 <= Znth j (sublist 0 m_pre values) 0 < 1000001).
  { eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH7 j Hj). lia. }
  assert (Hnot : ~ GoodWindow b_data (sublist 0 m_pre values) k_pre).
  { intro Hgood. apply (proj1 (good_window_iff_match_score__window_semantics
      b_data (sublist 0 m_pre values) need_data_2 have_data_2 matched k_pre
      Hblen Hbnd Hwbnd PreH16 PreH17 PreH18)) in Hgood. lia. }
  destruct (counted_good_windows_step__window_semantics k_pre values b_data
    0 0 ltac:(lia) (counted_good_windows_zero__window_semantics
      k_pre values b_data)) as [_ Hstep].
  replace (0 + Zlength b_data) with m_pre in Hstep by lia.
  replace (m_pre - m_pre + 1) with (0 + 1) by lia.
  exact (Hstep Hnot).
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with m_pre in PreH17 by lia.
  replace (m_pre - m_pre) with 0 by lia. exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_3 : solver_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto). apply PreH8; assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_4 : solver_entail_wit_5_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto). apply PreH7; assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH22 as [Htablelen Htablefreq].
  assert (Hout : 0 <= Znth (i - m_pre) values 0 < 1000001).
  { specialize (PreH11 (i - m_pre) ltac:(lia)). lia. }
  assert (Hin : 0 <= Znth i values 0 < 1000001).
  { specialize (PreH11 i ltac:(lia)). lia. }
  pose proof PreH2 as Hr4. pose proof PreH3 as Hr3.
  pose proof PreH4 as Hr2. pose proof PreH5 as Hr.
  unfold z_min in Hr4, Hr3, Hr2, Hr.
  rewrite Znth_replace_Znth_Same in Hr2 by lia.
  rewrite Znth_replace_Znth_Same in Hr4 by
    (rewrite Zlength_replace_Znth__window_semantics; lia).
  pose proof (table_match_score_updates_zmin__window_semantics need_data_2
    have_data_2 (Znth (i - m_pre) values 0) (Znth i values 0)
    (Znth (Znth (i - m_pre) values 0) have_data_2 0 - 1)
    (Znth (Znth i values 0)
      (replace_Znth (Znth (i - m_pre) values 0)
        (Znth (Znth (i - m_pre) values 0) have_data_2 0 - 1) have_data_2) 0 + 1)
    matched retval retval_2 retval_3 retval_4 Htablelen Hout Hin
    Hr Hr2 Hr3 Hr4 PreH23) as Hscore.
  pose proof (frequency_table_slide__window_semantics values have_data_2 i
    m_pre ltac:(lia) ltac:(lia) Hout Hin
    (conj Htablelen Htablefreq)) as Hfreq.
  assert (Hlen : Zlength b_data =
    Zlength (sublist (i + 1 - m_pre) (i + 1) values)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hbnd : forall j, 0 <= j < Zlength b_data ->
    0 <= Znth j b_data 0 < 1000001).
  { intros j Hj. specialize (PreH12 j Hj). lia. }
  assert (Hwbnd : forall j,
    0 <= j < Zlength (sublist (i + 1 - m_pre) (i + 1) values) ->
    0 <= Znth j (sublist (i + 1 - m_pre) (i + 1) values) 0 < 1000001).
  { eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH11 j Hj). lia. }
  assert (Hgood : GoodWindow b_data
    (sublist (i + 1 - m_pre) (i + 1) values) k_pre).
  { apply (proj2 (good_window_iff_match_score__window_semantics b_data
      (sublist (i + 1 - m_pre) (i + 1) values) need_data_2 _ _ k_pre
      Hlen Hbnd Hwbnd PreH21 Hfreq Hscore)). exact PreH1. }
  destruct (counted_good_windows_step__window_semantics k_pre values b_data
    (i - m_pre + 1) answer ltac:(lia) PreH24) as [Hstep _].
  replace (i - m_pre + 1 + Zlength b_data) with (i + 1) in Hstep by lia.
  replace (i - m_pre + 1) with (i + 1 - m_pre) in Hstep by lia.
  exact (Hstep Hgood).
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_2 : solver_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH22 as [Hlen Hfreq].
  assert (Hout : 0 <= Znth (i - m_pre) values 0 < 1000001).
  { specialize (PreH11 (i - m_pre) ltac:(lia)). lia. }
  assert (Hin : 0 <= Znth i values 0 < 1000001).
  { specialize (PreH11 i ltac:(lia)). lia. }
  unfold z_min in PreH2, PreH3, PreH4, PreH5.
  rewrite Znth_replace_Znth_Same in PreH4 by lia.
  rewrite Znth_replace_Znth_Same in PreH2 by
    (rewrite Zlength_replace_Znth__window_semantics; lia).
  eapply table_match_score_updates_zmin__window_semantics;
    [exact Hlen | exact Hout | exact Hin | exact PreH5 | exact PreH4 |
     exact PreH3 | exact PreH2 | exact PreH23].
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_3 : solver_entail_wit_6_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply frequency_table_slide__window_semantics.
  - lia.
  - lia.
  - specialize (PreH11 (i - m_pre) ltac:(lia)). lia.
  - specialize (PreH11 i ltac:(lia)). lia.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_4 : solver_entail_wit_6_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proof_of_solver_entail_wit_6_1_split_goal_2 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    retval_3 retval_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24) as Hscore.
  pose proof (proof_of_solver_entail_wit_6_1_split_goal_3 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    retval_3 retval_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24) as Hfreq.
  assert (Hb : Forall (fun x => 0 <= x < 1000001) b_data).
  { apply Forall_Znth_intro__window_semantics. intros j Hj.
    specialize (PreH12 j Hj). lia. }
  assert (Hw : Forall (fun x => 0 <= x < 1000001)
    (sublist (i + 1 - m_pre) (i + 1) values)).
  { apply Forall_Znth_intro__window_semantics.
    eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH11 j Hj). lia. }
  pose proof (table_match_score_bounds__window_semantics b_data
    (sublist (i + 1 - m_pre) (i + 1) values) need_data_2 _ _
    Hb Hw PreH21 Hfreq Hscore) as Hbounds.
  rewrite Zlength_sublist in Hbounds by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH22 as [Htablelen Htablefreq].
  assert (Hout : 0 <= Znth (i - m_pre) values 0 < 1000001).
  { specialize (PreH11 (i - m_pre) ltac:(lia)). lia. }
  assert (Hin : 0 <= Znth i values 0 < 1000001).
  { specialize (PreH11 i ltac:(lia)). lia. }
  pose proof PreH2 as Hr4. pose proof PreH3 as Hr3.
  pose proof PreH4 as Hr2. pose proof PreH5 as Hr.
  unfold z_min in Hr4, Hr3, Hr2, Hr.
  rewrite Znth_replace_Znth_Same in Hr2 by lia.
  rewrite Znth_replace_Znth_Same in Hr4 by
    (rewrite Zlength_replace_Znth__window_semantics; lia).
  pose proof (table_match_score_updates_zmin__window_semantics need_data_2
    have_data_2 (Znth (i - m_pre) values 0) (Znth i values 0)
    (Znth (Znth (i - m_pre) values 0) have_data_2 0 - 1)
    (Znth (Znth i values 0)
      (replace_Znth (Znth (i - m_pre) values 0)
        (Znth (Znth (i - m_pre) values 0) have_data_2 0 - 1) have_data_2) 0 + 1)
    matched retval retval_2 retval_3 retval_4 Htablelen Hout Hin
    Hr Hr2 Hr3 Hr4 PreH23) as Hscore.
  pose proof (frequency_table_slide__window_semantics values have_data_2 i
    m_pre ltac:(lia) ltac:(lia) Hout Hin
    (conj Htablelen Htablefreq)) as Hfreq.
  assert (Hlen : Zlength b_data =
    Zlength (sublist (i + 1 - m_pre) (i + 1) values)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hbnd : forall j, 0 <= j < Zlength b_data ->
    0 <= Znth j b_data 0 < 1000001).
  { intros j Hj. specialize (PreH12 j Hj). lia. }
  assert (Hwbnd : forall j,
    0 <= j < Zlength (sublist (i + 1 - m_pre) (i + 1) values) ->
    0 <= Znth j (sublist (i + 1 - m_pre) (i + 1) values) 0 < 1000001).
  { eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH11 j Hj). lia. }
  assert (Hnot : ~ GoodWindow b_data
    (sublist (i + 1 - m_pre) (i + 1) values) k_pre).
  { intro Hgood. apply (proj1 (good_window_iff_match_score__window_semantics
      b_data (sublist (i + 1 - m_pre) (i + 1) values) need_data_2 _ _
      k_pre Hlen Hbnd Hwbnd PreH21 Hfreq Hscore)) in Hgood. lia. }
  destruct (counted_good_windows_step__window_semantics k_pre values b_data
    (i - m_pre + 1) answer ltac:(lia) PreH24) as [_ Hstep].
  replace (i - m_pre + 1 + Zlength b_data) with (i + 1) in Hstep by lia.
  replace (i - m_pre + 1) with (i + 1 - m_pre) in Hstep by lia.
  exact (Hstep Hnot).
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_2 : solver_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH22 as [Hlen Hfreq].
  assert (Hout : 0 <= Znth (i - m_pre) values 0 < 1000001).
  { specialize (PreH11 (i - m_pre) ltac:(lia)). lia. }
  assert (Hin : 0 <= Znth i values 0 < 1000001).
  { specialize (PreH11 i ltac:(lia)). lia. }
  unfold z_min in PreH2, PreH3, PreH4, PreH5.
  rewrite Znth_replace_Znth_Same in PreH4 by lia.
  rewrite Znth_replace_Znth_Same in PreH2 by
    (rewrite Zlength_replace_Znth__window_semantics; lia).
  eapply table_match_score_updates_zmin__window_semantics;
    [exact Hlen | exact Hout | exact Hin | exact PreH5 | exact PreH4 |
     exact PreH3 | exact PreH2 | exact PreH23].
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_3 : solver_entail_wit_6_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply frequency_table_slide__window_semantics.
  - lia.
  - lia.
  - specialize (PreH11 (i - m_pre) ltac:(lia)). lia.
  - specialize (PreH11 i ltac:(lia)). lia.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_4 : solver_entail_wit_6_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proof_of_solver_entail_wit_6_2_split_goal_2 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    retval_3 retval_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24) as Hscore.
  pose proof (proof_of_solver_entail_wit_6_2_split_goal_3 b_data values
    n_pre m_pre k_pre have_data_2 need_data_2 answer matched i retval retval_2
    retval_3 retval_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24) as Hfreq.
  assert (Hb : Forall (fun x => 0 <= x < 1000001) b_data).
  { apply Forall_Znth_intro__window_semantics. intros j Hj.
    specialize (PreH12 j Hj). lia. }
  assert (Hw : Forall (fun x => 0 <= x < 1000001)
    (sublist (i + 1 - m_pre) (i + 1) values)).
  { apply Forall_Znth_intro__window_semantics.
    eapply sublist_Znth_bounds__window_semantics; [lia | lia |].
    intros j Hj. specialize (PreH11 j Hj). lia. }
  pose proof (table_match_score_bounds__window_semantics b_data
    (sublist (i + 1 - m_pre) (i + 1) values) need_data_2 _ _
    Hb Hw PreH21 Hfreq Hscore) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH8, PreH9 in *.
  assert (Hhave_len : Zlength have_data_2 = 1000001).
  { destruct PreH17 as [Hlen _]. exact Hlen. }
  pose proof
    (cleared_by_prefix_zero__cleanup_and_result values have_data_2 Hhave_len)
    as Hcleared.
  Exists have_data_2 have_data_2 need_data_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 <= i < Zlength values) by lia.
  assert (Hsource : forall j, 0 <= j <= i ->
      0 <= Znth j values 0 < 1000001).
  {
    intros j Hj.
    specialize (PreH6 j ltac:(lia)).
    lia.
  }
  pose proof
    (cleared_by_prefix_step__cleanup_and_result
      original_have_2 values have_data_2 i Hi Hsource PreH18)
    as Hcleared.
  Exists (replace_Znth (Znth i values 0) 0 have_data_2)
    original_have_2 need_data_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH8, PreH9 in *.
  assert (Hcoverage : forall j,
      0 <= j < Zlength
        (sublist (Zlength values - Zlength b_data) (Zlength values) values) ->
      exists q, 0 <= q < Zlength values /\
        Znth j
          (sublist (Zlength values - Zlength b_data) (Zlength values) values) 0 =
        Znth q values 0).
  {
    intros j Hj.
    rewrite Zlength_correct, sublist_length in Hj by lia.
    exists (j + (Zlength values - Zlength b_data)).
    split.
    - lia.
    - apply Znth_sublist; lia.
  }
  pose proof
    (cleared_frequency_table_complete__cleanup_and_result
      values
      (sublist (Zlength values - Zlength b_data) (Zlength values) values)
      original_have have_data PreH17 Hcoverage PreH18)
    as Hhave_zero.
  assert (Hneed_len : Zlength need_data_2 = 1000001).
  { destruct PreH16 as [Hlen _]. exact Hlen. }
  pose proof
    (cleared_by_prefix_zero__cleanup_and_result b_data need_data_2 Hneed_len)
    as Hneed_cleared.
  unfold repeat_Z.
  rewrite Hhave_zero.
  Exists need_data_2 need_data_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 <= i < Zlength b_data) by lia.
  assert (Hsource : forall j, 0 <= j <= i ->
      0 <= Znth j b_data 0 < 1000001).
  {
    intros j Hj.
    specialize (PreH7 j ltac:(lia)).
    lia.
  }
  pose proof
    (cleared_by_prefix_step__cleanup_and_result
      original_need_2 b_data need_data_2 i Hi Hsource PreH17)
    as Hcleared.
  Exists (replace_Znth (Znth i b_data 0) 0 need_data_2)
    original_need_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply counted_good_windows_spec_bridge__cleanup_and_result.
  rewrite <- PreH8, <- PreH9.
  exact PreH18.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_2 : solver_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia.
  subst i.
  rewrite PreH9 in PreH17.
  unfold repeat_Z.
  eapply cleared_frequency_table_complete__cleanup_and_result.
  - exact PreH16.
  - intros j Hj.
    exists j.
    split; [exact Hj | reflexivity].
  - exact PreH17.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_2.
Qed.
