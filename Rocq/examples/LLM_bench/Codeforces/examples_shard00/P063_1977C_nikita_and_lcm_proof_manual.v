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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P063_1977C_nikita_and_lcm_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P063_1977C_nikita_and_lcm_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P063_1977C_nikita_and_lcm_lib.
Local Open Scope sac.

Lemma proof_of_gcdll_entail_wit_2_split_goal_1 : gcdll_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in *.
  transitivity (Z.gcd a b).
  - apply gcd_mod_step_nonnegative__gcd_arithmetic; lia.
  - exact PreH5.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_2 : gcdll_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos a b ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_3 : gcdll_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos a b ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_gcdll_return_wit_1_split_goal_1 : gcdll_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst b.
  unfold GcdValue in *.
  rewrite Z.gcd_0_r in PreH5.
  rewrite Z.abs_eq in PreH5 by lia.
  exact PreH5.
Qed.

Lemma proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gcdll_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_lcm_cap_safety_wit_5_split_goal_1 : lcm_cap_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH8.
  subst g.
  destruct (gcd_positive_bounds__lcm_cap_contract a_pre b_pre PreH4 PreH6)
    as [Hg_pos [Hg_le_b Hg_div_a]].
  assert (Hg_le_a : Z.gcd a_pre b_pre <= a_pre).
  { apply Z.divide_pos_le; [lia | exact Hg_div_a]. }
  assert (Hquot_pos : 0 < a_pre ÷ Z.gcd a_pre b_pre).
  { rewrite Z.quot_div_exact; [apply Z.div_str_pos; lia | lia | exact Hg_div_a]. }
  assert (Hmul :
    (a_pre ÷ Z.gcd a_pre b_pre) * b_pre <=
    (cap_pre ÷ b_pre) * b_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  pose proof (Z.mul_quot_le cap_pre b_pre ltac:(lia) ltac:(lia)) as Hfloor.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_lcm_cap_safety_wit_5_split_goal_2 : lcm_cap_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH8.
  subst g.
  destruct (gcd_positive_bounds__lcm_cap_contract a_pre b_pre PreH4 PreH6)
    as [Hg_pos [Hg_le_b Hg_div_a]].
  assert (Hg_le_a : Z.gcd a_pre b_pre <= a_pre).
  { apply Z.divide_pos_le; [lia | exact Hg_div_a]. }
  assert (Hquot_pos : 0 < a_pre ÷ Z.gcd a_pre b_pre).
  { rewrite Z.quot_div_exact; [apply Z.div_str_pos; lia | lia | exact Hg_div_a]. }
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_lcm_cap_safety_wit_5 : lcm_cap_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcm_cap_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_lcm_cap_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_lcm_cap_entail_wit_1_split_goal_1 : lcm_cap_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH1.
  subst retval.
  destruct (gcd_positive_bounds__lcm_cap_contract a_pre b_pre PreH4 PreH6)
    as [Hg_pos [Hg_le_b Hg_div_a]].
  exact Hg_le_b.
Qed.

Lemma proof_of_lcm_cap_entail_wit_1_split_goal_2 : lcm_cap_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH1.
  subst retval.
  destruct (gcd_positive_bounds__lcm_cap_contract a_pre b_pre PreH4 PreH6)
    as [Hg_pos [Hg_le_b Hg_div_a]].
  exact Hg_pos.
Qed.

Lemma proof_of_lcm_cap_entail_wit_1 : lcm_cap_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcm_cap_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_lcm_cap_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_lcm_cap_return_wit_1_split_goal_1 : lcm_cap_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH9.
  subst g.
  unfold LcmCapValue.
  rewrite (lcm_as_gcd_quotient_product__lcm_cap_contract a_pre b_pre PreH5 PreH7).
  destruct (Z.leb ((a_pre ÷ Z.gcd a_pre b_pre) * b_pre) cap_pre) eqn:Hle.
  - apply Z.leb_le in Hle. lia.
  - reflexivity.
Qed.

Lemma proof_of_lcm_cap_return_wit_1 : lcm_cap_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcm_cap_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_lcm_cap_return_wit_2_split_goal_1 : lcm_cap_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH9.
  subst g.
  unfold LcmCapValue.
  rewrite (lcm_as_gcd_quotient_product__lcm_cap_contract a_pre b_pre PreH5 PreH7).
  destruct (Z.leb ((a_pre ÷ Z.gcd a_pre b_pre) * b_pre) cap_pre) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.

Lemma proof_of_lcm_cap_return_wit_2_split_goal_2 : lcm_cap_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH9.
  subst g.
  destruct (gcd_positive_bounds__lcm_cap_contract a_pre b_pre PreH5 PreH7)
    as [Hg_pos [Hg_le_b Hg_div_a]].
  assert (Hg_le_a : Z.gcd a_pre b_pre <= a_pre).
  { apply Z.divide_pos_le; [lia | exact Hg_div_a]. }
  assert (Hquot_pos : 0 < a_pre ÷ Z.gcd a_pre b_pre).
  { rewrite Z.quot_div_exact; [apply Z.div_str_pos; lia | lia | exact Hg_div_a]. }
  nia.
Qed.

Lemma proof_of_lcm_cap_return_wit_2 : lcm_cap_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcm_cap_return_wit_2_split_goal_1.
  - Goal_apply proof_of_lcm_cap_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_lcm_cap_return_wit_3_split_goal_1 : lcm_cap_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH8.
  subst g.
  unfold LcmCapValue.
  rewrite (lcm_as_gcd_quotient_product__lcm_cap_contract a_pre b_pre PreH4 PreH6).
  pose proof (Z.mul_succ_quot_gt cap_pre b_pre ltac:(lia) ltac:(lia)) as Hnext.
  assert (Hproduct : cap_pre < (a_pre ÷ Z.gcd a_pre b_pre) * b_pre) by nia.
  destruct (Z.leb ((a_pre ÷ Z.gcd a_pre b_pre) * b_pre) cap_pre) eqn:Hle.
  - apply Z.leb_le in Hle. lia.
  - reflexivity.
Qed.

Lemma proof_of_lcm_cap_return_wit_3 : lcm_cap_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcm_cap_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmp_int_return_wit_1_split_goal_1 : cmp_int_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CompareResult.
  right; right; split; lia.
Qed.

Lemma proof_of_cmp_int_return_wit_1 : cmp_int_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_int_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmp_int_return_wit_2_split_goal_1 : cmp_int_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CompareResult.
  right; left; split; lia.
Qed.

Lemma proof_of_cmp_int_return_wit_2 : cmp_int_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_int_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmp_int_return_wit_3_split_goal_1 : cmp_int_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CompareResult.
  left; split; lia.
Qed.

Lemma proof_of_cmp_int_return_wit_3 : cmp_int_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_int_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH3.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst original.
  unfold CopyMaxState, sublist.
  simpl.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst original.
  assert (Hcopied_len : Zlength copied_2 = i).
  { unfold CopyMaxState in PreH12.
    destruct PreH12 as [Hcopied _].
    rewrite Hcopied.
    rewrite Zlength_sublist by lia.
    lia. }
  assert (Hlast :
    Znth (i - 0) (copied_2 ++ (Znth i a 0 :: nil)) 0 = Znth i a 0).
  { rewrite Z.sub_0_r.
    rewrite app_Znth2 by lia.
    rewrite Hcopied_len, Z.sub_diag.
    reflexivity. }
  rewrite Hlast.
  apply (copy_max_state_step_high__copy_loop a copied_2 i mx);
    try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_2 : solver_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst original.
  assert (Hcopied_len : Zlength copied_2 = i).
  { unfold CopyMaxState in PreH12.
    destruct PreH12 as [Hcopied _].
    rewrite Hcopied.
    rewrite Zlength_sublist by lia.
    lia. }
  rewrite Z.sub_0_r.
  rewrite app_Znth2 by lia.
  rewrite Hcopied_len, Z.sub_diag.
  rewrite Znth0_cons.
  specialize (PreH7 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst original.
  assert (Hcopied_len : Zlength copied_2 = i).
  { unfold CopyMaxState in PreH12.
    destruct PreH12 as [Hcopied _].
    rewrite Hcopied.
    rewrite Zlength_sublist by lia.
    lia. }
  assert (Hlast :
    Znth (i - 0) (copied_2 ++ (Znth i a 0 :: nil)) 0 = Znth i a 0).
  { rewrite Z.sub_0_r.
    rewrite app_Znth2 by lia.
    rewrite Hcopied_len, Z.sub_diag.
    reflexivity. }
  rewrite Hlast in PreH1.
  apply copy_max_state_step_low__copy_loop; try assumption.
  - lia.
  - specialize (PreH7 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfinished : finished_i = n_pre) by lia.
  destruct (copy_max_state_complete__copy_exit
    original copied finished_i mx ltac:(lia) ltac:(lia) PreH11
    ltac:(intros k Hk; apply PreH6; lia)) as (_ & _ & _ & Hmx).
  unfold LcmPrefixState.
  exists 1.
  split.
  - apply least_common_empty_is_one__copy_exit.
  - assert (Htest : Z.leb 1 mx = true) by (apply Z.leb_le; lia).
    rewrite Htest.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfinished : finished_i = n_pre) by lia.
  subst finished_i.
  subst a.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (copy_max_state_complete__copy_exit
    original copied finished_i mx ltac:(lia) ltac:(lia) PreH11
    ltac:(intros k Hk; apply PreH6; lia)) as (_ & _ & _ & Hmx).
  exact Hmx.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (copy_max_state_complete__copy_exit
    original copied finished_i mx ltac:(lia) ltac:(lia) PreH11
    ltac:(intros k Hk; apply PreH6; lia)) as (_ & _ & Hcopied_bounds & _).
  apply Hcopied_bounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_6 : solver_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (copy_max_state_complete__copy_exit
    original copied finished_i mx ltac:(lia) ltac:(lia) PreH11
    ltac:(intros k Hk; apply PreH6; lia)) as (_ & Hcopied_length & _).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply least_common_prefix_extend__lcm_prefix; eauto.
  apply PreH11. lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  subst a.
  eapply (full_lcm_outside_array_spec__lcm_prefix
            original copied n_pre mx_2 all); eassumption.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  subst mx_2.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply permutation_preserves_pointwise_bounds__lcm_prefix; eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst a.
  apply divisor_best_initial__divisor_init.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10. assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9. assumption.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH18. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH17. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst all_3.
  assert (Hz : z = 0 \/ z = 1) by lia.
  destruct Hz as [-> | ->].
  - rewrite Znth0_cons.
    apply divisor_scan_initial__divisor_init. lia.
  - rewrite Znth_cons by lia.
    rewrite Znth0_cons.
    apply divisor_scan_initial__divisor_init.
    destruct (two_divisors_bounds__divisor_init mx_4 q_2 PreH11 PreH13 PreH14)
      as [_ [Hlow _]].
    exact Hlow.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_2 : solver_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH20. assumption.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_3 : solver_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH19. assumption.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_4 : solver_entail_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst all_3.
  assert (Hz : z = 0 \/ z = 1) by lia.
  destruct Hz as [-> | ->].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite Znth0_cons.
    destruct (two_divisors_bounds__divisor_init mx_4 q_2 PreH11 PreH13 PreH14)
      as [_ [Hlow _]].
    lia.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_5 : solver_entail_wit_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst all_3.
  assert (Hz : z = 0 \/ z = 1) by lia.
  destruct Hz as [-> | ->].
  - rewrite Znth0_cons.
    destruct (two_divisors_bounds__divisor_init mx_4 q_2 PreH11 PreH13 PreH14)
      as [[_ Hhigh] _].
    exact Hhigh.
  - rewrite Znth_cons by lia.
    rewrite Znth0_cons.
    destruct (two_divisors_bounds__divisor_init mx_4 q_2 PreH11 PreH13 PreH14)
      as [_ [_ Hhigh]].
    exact Hhigh.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_6 : solver_entail_wit_10_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst all_3.
  assert (Hz : z = 0 \/ z = 1) by lia.
  destruct Hz as [-> | ->].
  - rewrite Znth0_cons. exact PreH11.
  - rewrite Znth_cons by lia.
    rewrite Znth0_cons.
    destruct (two_divisors_bounds__divisor_init mx_4 q_2 PreH11 PreH13 PreH14)
      as [_ [Hlow _]].
    exact Hlow.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
  specialize (PreH36 i_2 ltac:(lia)).
  destruct PreH36 as [Hvalue_pos _].
  pose proof (positive_divisor_le__divisor_scan
    (Znth i_2 sorted 0) d Hvalue_pos PreH23 PreH4) as [Hdiv _].
  eapply divisor_scan_step_dividing__divisor_scan.
  - exact PreH27.
  - exact PreH23.
  - exact Hvalue_pos.
  - exact Hdiv.
  - exact PreH3.
  - exact PreH41.
  - left. split; [exact PreH5 | reflexivity].
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
  specialize (PreH36 i_2 ltac:(lia)).
  destruct PreH36 as [Hvalue_pos _].
  pose proof (positive_divisor_le__divisor_scan
    (Znth i_2 sorted 0) d Hvalue_pos PreH23 PreH4) as [Hdiv _].
  eapply divisor_scan_step_dividing__divisor_scan.
  - exact PreH27.
  - exact PreH23.
  - exact Hvalue_pos.
  - exact Hdiv.
  - exact PreH3.
  - exact PreH41.
  - right. split; [exact PreH5 | reflexivity].
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_1 : solver_entail_wit_11_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
  exfalso.
  apply PreH1.
  rewrite PreH2.
  apply Z.rem_same.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_1 : solver_entail_wit_11_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
  specialize (PreH33 i_2 ltac:(lia)).
  destruct PreH33 as [Hvalue_pos _].
  assert (Hnotdiv : ~ (Znth i_2 sorted 0 | d)).
  {
    intro Hdiv.
    apply PreH1.
    pose proof (Z.rem_divide d (Znth i_2 sorted 0) ltac:(lia)) as Hiff.
    apply (proj2 Hiff). exact Hdiv.
  }
  eapply divisor_scan_step_nondividing__divisor_scan.
  - exact PreH24.
  - exact PreH2.
  - exact Hnotdiv.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  repeat match goal with
  | H : Z.rem ?x ?y = 0 |- _ =>
      rewrite Z.rem_mod_nonneg in H by lia
  end.
  repeat match goal with
  | H : context [Z.quot ?x ?y] |- _ =>
      rewrite Z.quot_div_nonneg in H by lia
  end.
  try subst original.
  try subst all_3.
  assert (Hperm : Permutation a sorted).
  { eapply copy_max_full_permutation__candidate_update; eauto. }
  assert (Hcandidate : DivisorCandidateCount a d count).
  { eapply (completed_scan_candidate__candidate_update
      a sorted d i_2 present count l); eauto; lia. }
  apply (divisor_best_add_score__candidate_update
    a mx_4 q_2 z d ans_3 count).
  - lia.
  - exact PreH17.
  - exact PreH16.
  - exact PreH20.
  - exact PreH38.
  - exact Hcandidate.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  repeat match goal with
  | H : Z.rem ?x ?y = 0 |- _ =>
      rewrite Z.rem_mod_nonneg in H by lia
  end.
  repeat match goal with
  | H : context [Z.quot ?x ?y] |- _ =>
      rewrite Z.quot_div_nonneg in H by lia
  end.
  try subst original.
  try subst all_3.
  assert (Hperm : Permutation a sorted).
  { eapply copy_max_full_permutation__candidate_update; eauto. }
  assert (Hineligible : forall score, ~ DivisorCandidateCount a d score).
  { eapply (completed_scan_l_ineligible__candidate_update
      a sorted d i_2 present count l); eauto; lia. }
  eapply (divisor_best_skip_score__candidate_update
    a mx_4 q_2 z d ans_2); eauto; try lia.
  intros score Hscore. exfalso. eapply Hineligible. exact Hscore.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_1 : solver_entail_wit_12_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  repeat match goal with
  | H : Z.rem ?x ?y = 0 |- _ =>
      rewrite Z.rem_mod_nonneg in H by lia
  end.
  repeat match goal with
  | H : context [Z.quot ?x ?y] |- _ =>
      rewrite Z.quot_div_nonneg in H by lia
  end.
  try subst original.
  try subst all_3.
  assert (Hperm : Permutation a sorted).
  { eapply copy_max_full_permutation__candidate_update; eauto. }
  assert (Hineligible : forall score, ~ DivisorCandidateCount a d score).
  { eapply (completed_scan_present_ineligible__candidate_update
      a sorted d i_2 present count l); eauto; lia. }
  eapply (divisor_best_skip_score__candidate_update
    a mx_4 q_2 z d ans_2); eauto; try lia.
  intros score Hscore. exfalso. eapply Hineligible. exact Hscore.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_1 : solver_entail_wit_12_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  repeat match goal with
  | H : Z.rem ?x ?y = 0 |- _ =>
      rewrite Z.rem_mod_nonneg in H by lia
  end.
  repeat match goal with
  | H : context [Z.quot ?x ?y] |- _ =>
      rewrite Z.quot_div_nonneg in H by lia
  end.
  try subst original.
  try subst all_3.
  assert (Hperm : Permutation a sorted).
  { eapply copy_max_full_permutation__candidate_update; eauto. }
  assert (Hcandidate : DivisorCandidateCount a d count).
  { eapply (completed_scan_candidate__candidate_update
      a sorted d i_2 present count l); eauto; lia. }
  eapply (divisor_best_skip_score__candidate_update
    a mx_4 q_2 z d ans_2); eauto; try lia.
  intros score Hscore.
  assert (score = count).
  { eapply divisor_candidate_count_unique__candidate_update; eauto. }
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcopied : copied = original).
  {
    unfold CopyMaxState in PreH18.
    destruct PreH18 as [Hcopied _].
    rewrite (sublist_self original n_pre PreH3) in Hcopied.
    exact Hcopied.
  }
  assert (Hfull : LeastCommonOfChosen original
    (fun idx : Z => 0 <= idx < Zlength original) mx_3).
  {
    unfold LcmPrefixState in PreH19.
    destruct PreH19 as [exact [Hlcm Hacc]].
    rewrite PreH10 in Hacc.
    destruct ((exact <=? mx_3)%Z) eqn:Hexact.
    - apply Z.leb_le in Hexact.
      assert (exact = mx_3) by lia.
      subst exact. rewrite Hcopied, PreH3 in Hlcm. exact Hlcm.
    - lia.
  }
  subst a.
  apply divisor_best_complete_implies_spec__final_result
    with (mx := mx_3) (q := q); assumption.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst a. subst all_2.
  apply (divisor_best_advance_dividing__outer_transition
           original mx_3 q z ans).
  - exact PreH11.
  - exact PreH13.
  - exact PreH14.
  - apply Z.ge_le. exact PreH1.
  - exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst a. subst all_2.
  apply (divisor_best_advance_nondividing__outer_transition
           original mx_3 q ans).
  - exact PreH12.
  - exact PreH1.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure_split_goal_1 : solver_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyMaxState in PreH17.
  destruct PreH17 as [Hcopied _].
  dump_pre_spatial.
  rewrite Hcopied.
  rewrite Zlength_sublist0 by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_6_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_8_pure_split_goal_1 : solver_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (copy_max_full_upper__lcm_prefix
       original copied n_pre mx i ltac:(lia) PreH23) as Hupper.
  dump_pre_spatial.
  exact Hupper.
Qed.

Lemma proof_of_solver_partial_solve_wit_8_pure : solver_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_8_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_18_pure_split_goal_1 : solver_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
  specialize (PreH55 i ltac:(lia)).
  destruct PreH55 as [Hvalue_pos _].
  pose proof (positive_divisor_le__divisor_scan
    (Znth i sorted 0) d Hvalue_pos PreH42 PreH23) as [_ Hle].
  dump_pre_spatial.
  exact Hle.
Qed.

Lemma proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_18_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst finished_i.
  sep_apply_l_atomic (IntArray.seg_to_full a 0 n_pre copied).
  replace (a + 0 * sizeof(INT)) with a by lia.
  replace (n_pre - 0) with n_pre by lia.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed.
