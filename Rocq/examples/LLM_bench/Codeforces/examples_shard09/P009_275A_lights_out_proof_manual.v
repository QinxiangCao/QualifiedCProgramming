From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P009_275A_lights_out_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P009_275A_lights_out_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P009_275A_lights_out_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold lights_dj.
  assert (Hd5 : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4) by lia.
  destruct Hd5 as [-> | [-> | [-> | [-> | ->]]]].
  all: repeat (rewrite Znth_cons by lia).
  all: rewrite Znth0_cons.
  all: lia.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold lights_dj.
  assert (Hd5 : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4) by lia.
  destruct Hd5 as [-> | [-> | [-> | [-> | ->]]]].
  all: repeat (rewrite Znth_cons by lia).
  all: rewrite Znth0_cons.
  all: lia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_21_split_goal_1 : solver_safety_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold lights_di.
  assert (Hd5 : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4) by lia.
  destruct Hd5 as [-> | [-> | [-> | [-> | ->]]]].
  all: repeat (rewrite Znth_cons by lia).
  all: rewrite Znth0_cons.
  all: lia.
Qed.

Lemma proof_of_solver_safety_wit_21_split_goal_2 : solver_safety_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold lights_di.
  assert (Hd5 : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4) by lia.
  destruct Hd5 as [-> | [-> | [-> | [-> | ->]]]].
  all: repeat (rewrite Znth_cons by lia).
  all: rewrite Znth0_cons.
  all: lia.
Qed.

Lemma proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_21_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_21_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (PreH8 (i + Znth d lights_di 0) (j + Znth d lights_dj 0)
       ltac:(lia)) as Hcell.
  destruct Hcell as [Hcell_nonneg Hcell_upper].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (PreH8 (i + Znth d lights_di 0) (j + Znth d lights_dj 0)
       ltac:(lia)) as Hcell.
  destruct Hcell as [Hcell_nonneg Hcell_upper].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
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
  replace (3 * i + 0) with (3 * i) by lia.
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
  unfold TogglePrefix. left. split; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : TogglePrefix g i j d tog |- _ =>
      pose proof
        (toggle_prefix_add_in_bounds__toggle_transitions g i j d tog
           ltac:(lia) H) as Hstep
  end.
  unfold cell in Hstep.
  replace ((0 <=? i + Znth d lights_di 0)%Z) with true in Hstep by
    (symmetry; apply Z.leb_le; lia).
  replace ((0 <=? j + Znth d lights_dj 0)%Z) with true in Hstep by
    (symmetry; apply Z.leb_le; lia).
  cbn [andb] in Hstep.
  rewrite (Znth_indep__output_write _ g (i + Znth d lights_di 0)
             (@nil Z) __default__List_Z) in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (toggle_prefix_bounds__valid_neighbor_a g __default__List_Z i j d tog
       PreH6 PreH7 PreH8 PreH17) as Hprefix.
  pose proof
    (PreH8 (i + Znth d lights_di 0) (j + Znth d lights_dj 0)
       ltac:(lia)) as Hcell.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall r c : Z, _ |- _ =>
      pose proof (H (i + Znth d lights_di 0) (j + Znth d lights_dj 0)
                    ltac:(lia)) as Hcell
  end.
  lia.
Qed.


Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply toggle_prefix_skip_out_of_bounds__toggle_transitions;
    [ lia | eassumption |].
  eapply (cell_out_of_range__toggle_skip g __default__List_Z);
    [ assumption | assumption | lia ].
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply toggle_prefix_skip_out_of_bounds__toggle_transitions;
    [ lia | eassumption |].
  eapply (cell_out_of_range__toggle_skip g __default__List_Z);
    [ assumption | assumption | lia ].
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_4_split_goal_1 : solver_entail_wit_4_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply toggle_prefix_skip_out_of_bounds__toggle_transitions;
    [ lia | eassumption |].
  eapply (cell_out_of_range__toggle_skip g __default__List_Z);
    [ assumption | assumption | lia ].
Qed.

Lemma proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_5_split_goal_1 : solver_entail_wit_4_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply toggle_prefix_skip_out_of_bounds__toggle_transitions;
    [ lia | eassumption |].
  eapply (cell_out_of_range__toggle_skip g __default__List_Z);
    [ assumption | assumption | lia ].
Qed.

Lemma proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj3 : j = 3) by lia. subst j.
  replace (3 * (i + 1)) with (3 * i + 3) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_2 : solver_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_spatial : solver_entail_wit_6_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hd : d = 5) by lia. subst d.
  unfold TogglePrefix in PreH14.
  assert (Htog : tog = toggles g i j) by (destruct PreH14 as
    [[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[_ H]]]]]]; try lia; exact H).
  assert (Hbit : output_bit g i j = 0).
  { unfold output_bit. rewrite <- Htog.
    rewrite (odd_of_nonnegative_rem_nonzero__row1_write tog) by (lia || assumption).
    reflexivity. }
  replace (@Some Z 0) with (@Some Z (output_bit g i j))
    by (rewrite Hbit; reflexivity).
  rewrite (Znth_indep__output_write _ (staged_output g (3 * i + j)) i
             __default__List__App_option_Z nil)
    by (unfold staged_output; rewrite Zlength_correct; simpl; lia).
  unfold Array2.replace_mixed_row.
  rewrite staged_output_advance by lia.
  replace (3 * i + (j + 1)) with (3 * i + j + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_2 : solver_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_spatial : solver_entail_wit_6_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hd : d = 5) by lia. subst d.
  unfold TogglePrefix in PreH14.
  assert (Htog : tog = toggles g i j) by (destruct PreH14 as
    [[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[_ H]]]]]]; try lia; exact H).
  assert (Hbit : output_bit g i j = 1).
  { unfold output_bit. rewrite <- Htog.
    rewrite (even_of_nonnegative_rem_zero__row1_write tog) by (lia || assumption).
    reflexivity. }
  replace (@Some Z 1) with (@Some Z (output_bit g i j))
    by (rewrite Hbit; reflexivity).
  rewrite (Znth_indep__output_write _ (staged_output g (3 * i + j)) i
             __default__List__App_option_Z nil)
    by (unfold staged_output; rewrite Zlength_correct; simpl; lia).
  unfold Array2.replace_mixed_row.
  rewrite staged_output_advance by lia.
  replace (3 * i + (j + 1)) with (3 * i + j + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (out_grid g).
  assert (Hi : i = 3) by lia. subst i.
  replace (3 * 3) with 9 by lia.
  rewrite staged_output_final.
  replace (map (map (@Some Z)) (out_grid g))
    with (Array2.some_rows (out_grid g)) by reflexivity.
  sep_apply_l_atomic
    (Array2Convert.int_mixed_full_to_full out_pre 3 3 (out_grid g)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. apply spec_out_grid.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite staged_output_init.
  sep_apply_l_atomic (Array2Convert.int_undef_full_to_mixed_full out_pre 3 3).
  unfold Array2Convert.undef_rows.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed.
