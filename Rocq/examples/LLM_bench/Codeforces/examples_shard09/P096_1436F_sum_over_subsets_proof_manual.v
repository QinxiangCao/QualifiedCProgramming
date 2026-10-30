From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P096_1436F_sum_over_subsets_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P096_1436F_sum_over_subsets_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P096_1436F_sum_over_subsets_lib.
Local Open Scope sac.

Lemma proof_of_powmod_entail_wit_1_1_split_goal_1 : powmod_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_small_pos__powmod_modexp b_pre ltac:(lia) ltac:(lia)) as Hrs.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_1_split_goal_2 : powmod_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_small_pos__powmod_modexp b_pre ltac:(lia) ltac:(lia)) as Hrs.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_1 : powmod_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_1_1_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_1_1_split_goal_2.
Qed.

Lemma proof_of_powmod_entail_wit_1_2_split_goal_1 : powmod_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply powmod_init_state__powmod_modexp; lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_2_split_goal_2 : powmod_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_small_pos__powmod_modexp b_pre ltac:(lia) ltac:(lia)) as Hrs.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_2 : powmod_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_1_2_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_1_2_split_goal_2.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_1 : powmod_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply powmod_odd_state__powmod_modexp; try assumption; try lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_2 : powmod_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_bound__powmod_modexp (r * b) ltac:(nia)) as Hrb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_3 : powmod_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_bound__powmod_modexp (r * b) ltac:(nia)) as Hrb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_4 : powmod_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_bound__powmod_modexp (b * b) ltac:(nia)) as Hrb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_5 : powmod_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_bound__powmod_modexp (b * b) ltac:(nia)) as Hrb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_6 : powmod_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (shiftr_bound__powmod_modexp e ltac:(lia)) as Hsb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_7 : powmod_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (shiftr_bound__powmod_modexp e ltac:(lia)) as Hsb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1 : powmod_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_6.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_7.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_1 : powmod_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply powmod_even_state__powmod_modexp; try assumption; try lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_2 : powmod_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_bound__powmod_modexp (b * b) ltac:(nia)) as Hrb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_3 : powmod_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rem_bound__powmod_modexp (b * b) ltac:(nia)) as Hrb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_4 : powmod_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (shiftr_bound__powmod_modexp e ltac:(lia)) as Hsb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_5 : powmod_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (shiftr_bound__powmod_modexp e ltac:(lia)) as Hsb.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2 : powmod_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_5.
Qed.

Lemma proof_of_powmod_return_wit_1_split_goal_1 : powmod_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : PowmodState _ _ _ _ _ |- _ =>
      apply (powmod_final_state__powmod_modexp _ _ _ _ _ H); lia
  end.
Qed.

Lemma proof_of_powmod_return_wit_1 : powmod_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_powmod_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_pool_sum_safety_wit_4_split_goal_1 : pool_sum_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)) as Hb.
  change (Z.abs 998244353) with 998244353 in Hb.
  apply Z.abs_lt in Hb.
  lia.
Qed.

Lemma proof_of_pool_sum_safety_wit_4_split_goal_2 : pool_sum_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)) as Hb.
  change (Z.abs 998244353) with 998244353 in Hb.
  apply Z.abs_lt in Hb.
  lia.
Qed.

Lemma proof_of_pool_sum_safety_wit_4 : pool_sum_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_15_split_goal_1 : pool_sum_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  assert (H2 : 0 <= S2_pre % 998244353 * retval) by nia.
  pose proof (Z.rem_bound_pos (S2_pre % 998244353 * retval) 998244353 H2 ltac:(lia)) as H3.
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)) as H4.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_15_split_goal_2 : pool_sum_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  assert (H2 : 0 <= S2_pre % 998244353 * retval) by nia.
  pose proof (Z.rem_bound_pos (S2_pre % 998244353 * retval) 998244353 H2 ltac:(lia)) as H3.
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)) as H4.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_15 : pool_sum_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_19_split_goal_1 : pool_sum_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_19_split_goal_2 : pool_sum_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_19 : pool_sum_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_28_split_goal_1 : pool_sum_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)) as H1.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_28_split_goal_2 : pool_sum_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)) as H1.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_28 : pool_sum_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_29_split_goal_1 : pool_sum_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)) as H1.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_29_split_goal_2 : pool_sum_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)) as H1.
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_29 : pool_sum_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_39_split_goal_1 : pool_sum_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem S2_pre 998244353 * retval) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (Z.rem S2_pre 998244353 * retval) 998244353 * Z.rem (k_pre - 1) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (retval + retval_2 * Z.rem (k_pre - 2) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_39_split_goal_2 : pool_sum_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem S2_pre 998244353 * retval) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (Z.rem S2_pre 998244353 * retval) 998244353 * Z.rem (k_pre - 1) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (retval + retval_2 * Z.rem (k_pre - 2) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_39 : pool_sum_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_40_split_goal_1 : pool_sum_safety_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (retval + retval_2 * Z.rem (k_pre - 2) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_40_split_goal_2 : pool_sum_safety_wit_40_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (retval + retval_2 * Z.rem (k_pre - 2) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_40 : pool_sum_safety_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_40_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_40_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_43_split_goal_1 : pool_sum_safety_wit_43_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem S2_pre 998244353 * retval) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (Z.rem S2_pre 998244353 * retval) 998244353 * Z.rem (k_pre - 1) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_43_split_goal_2 : pool_sum_safety_wit_43_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem S2_pre 998244353 * retval) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (Z.rem S2_pre 998244353 * retval) 998244353 * Z.rem (k_pre - 1) 998244353) 998244353 ltac:(nia) ltac:(lia)).
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_43 : pool_sum_safety_wit_43.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_43_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_43_split_goal_2.
Qed.

Lemma proof_of_pool_sum_safety_wit_44_split_goal_1 : pool_sum_safety_wit_44_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_44_split_goal_2 : pool_sum_safety_wit_44_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)).
  pose proof (Z.rem_bound_pos (Z.rem (S_pre * S_pre - S2_pre) 998244353 + 998244353) 998244353 ltac:(lia) ltac:(lia)).
  nia.
Qed.

Lemma proof_of_pool_sum_safety_wit_44 : pool_sum_safety_wit_44.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_safety_wit_44_split_goal_1.
  - Goal_apply proof_of_pool_sum_safety_wit_44_split_goal_2.
Qed.

Lemma proof_of_pool_sum_return_wit_1_split_goal_1 : pool_sum_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  assert (H2 : 0 <= S2_pre % 998244353 * retval) by nia.
  pose proof (Z.rem_bound_pos (S2_pre % 998244353 * retval) 998244353 H2 ltac:(lia)) as H3.
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)) as H4.
  assert (H5 : 0 <= (S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) by nia.
  pose proof (Z.rem_bound_pos ((S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) 998244353 H5 ltac:(lia)) as H6.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)) as Hc.
  change (Z.abs 998244353) with 998244353 in Hc.
  apply Z.abs_lt in Hc.
  assert (Hc2 : 0 <= (S_pre * S_pre - S2_pre) % 998244353 + 998244353) by lia.
  pose proof (Z.rem_bound_pos ((S_pre * S_pre - S2_pre) % 998244353 + 998244353) 998244353 Hc2 ltac:(lia)) as Hc3.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)) as H7.
  assert (H8 : 0 <= retval + retval_2 * ((k_pre - 2) % 998244353)) by nia.
  pose proof (Z.rem_bound_pos (retval + retval_2 * ((k_pre - 2) % 998244353)) 998244353 H8 ltac:(lia)) as H9.
  apply rem_lt__pool_sum_closed_form; [ nia | lia ].
Qed.

Lemma proof_of_pool_sum_return_wit_1_split_goal_2 : pool_sum_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  assert (H2 : 0 <= S2_pre % 998244353 * retval) by nia.
  pose proof (Z.rem_bound_pos (S2_pre % 998244353 * retval) 998244353 H2 ltac:(lia)) as H3.
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)) as H4.
  assert (H5 : 0 <= (S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) by nia.
  pose proof (Z.rem_bound_pos ((S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) 998244353 H5 ltac:(lia)) as H6.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)) as Hc.
  change (Z.abs 998244353) with 998244353 in Hc.
  apply Z.abs_lt in Hc.
  assert (Hc2 : 0 <= (S_pre * S_pre - S2_pre) % 998244353 + 998244353) by lia.
  pose proof (Z.rem_bound_pos ((S_pre * S_pre - S2_pre) % 998244353 + 998244353) 998244353 Hc2 ltac:(lia)) as Hc3.
  pose proof (Z.rem_bound_pos (k_pre - 2) 998244353 ltac:(lia) ltac:(lia)) as H7.
  assert (H8 : 0 <= retval + retval_2 * ((k_pre - 2) % 998244353)) by nia.
  pose proof (Z.rem_bound_pos (retval + retval_2 * ((k_pre - 2) % 998244353)) 998244353 H8 ltac:(lia)) as H9.
  apply rem_ge__pool_sum_closed_form; [ nia | lia ].
Qed.

Lemma proof_of_pool_sum_return_wit_1_split_goal_3 : pool_sum_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pool_closed_form_from_residues__pool_sum_closed_form; try lia; assumption.
Qed.

Lemma proof_of_pool_sum_return_wit_1 : pool_sum_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_return_wit_1_split_goal_1.
  - Goal_apply proof_of_pool_sum_return_wit_1_split_goal_2.
  - Goal_apply proof_of_pool_sum_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_pool_sum_return_wit_2_split_goal_1 : pool_sum_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  assert (H2 : 0 <= S2_pre % 998244353 * retval) by nia.
  pose proof (Z.rem_bound_pos (S2_pre % 998244353 * retval) 998244353 H2 ltac:(lia)) as H3.
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)) as H4.
  assert (H5 : 0 <= (S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) by nia.
  pose proof (Z.rem_bound_pos ((S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) 998244353 H5 ltac:(lia)) as H6.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)) as Hc.
  change (Z.abs 998244353) with 998244353 in Hc.
  apply Z.abs_lt in Hc.
  assert (Hc2 : 0 <= (S_pre * S_pre - S2_pre) % 998244353 + 998244353) by lia.
  pose proof (Z.rem_bound_pos ((S_pre * S_pre - S2_pre) % 998244353 + 998244353) 998244353 Hc2 ltac:(lia)) as Hc3.
  apply rem_lt__pool_sum_closed_form; [ nia | lia ].
Qed.

Lemma proof_of_pool_sum_return_wit_2_split_goal_2 : pool_sum_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos S2_pre 998244353 ltac:(lia) ltac:(lia)) as H1.
  assert (H2 : 0 <= S2_pre % 998244353 * retval) by nia.
  pose proof (Z.rem_bound_pos (S2_pre % 998244353 * retval) 998244353 H2 ltac:(lia)) as H3.
  pose proof (Z.rem_bound_pos (k_pre - 1) 998244353 ltac:(lia) ltac:(lia)) as H4.
  assert (H5 : 0 <= (S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) by nia.
  pose proof (Z.rem_bound_pos ((S2_pre % 998244353 * retval) % 998244353 * ((k_pre - 1) % 998244353)) 998244353 H5 ltac:(lia)) as H6.
  pose proof (Z.rem_bound_abs (S_pre * S_pre - S2_pre) 998244353 ltac:(lia)) as Hc.
  change (Z.abs 998244353) with 998244353 in Hc.
  apply Z.abs_lt in Hc.
  assert (Hc2 : 0 <= (S_pre * S_pre - S2_pre) % 998244353 + 998244353) by lia.
  pose proof (Z.rem_bound_pos ((S_pre * S_pre - S2_pre) % 998244353 + 998244353) 998244353 Hc2 ltac:(lia)) as Hc3.
  apply rem_ge__pool_sum_closed_form; [ nia | lia ].
Qed.

Lemma proof_of_pool_sum_return_wit_2_split_goal_3 : pool_sum_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pool_closed_form_k2__pool_sum_closed_form.
  - lia.
  - rewrite PreH2. unfold pow_mod.
    replace (k_pre - 2) with 0 by lia. reflexivity.
  - lia.
  - lia.
Qed.

Lemma proof_of_pool_sum_return_wit_2 : pool_sum_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pool_sum_return_wit_2_split_goal_1.
  - Goal_apply proof_of_pool_sum_return_wit_2_split_goal_2.
  - Goal_apply proof_of_pool_sum_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_pool_sum_return_wit_3_split_goal_1 : pool_sum_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pool_closed_form_small__pool_sum_closed_form. lia.
Qed.

Lemma proof_of_pool_sum_return_wit_3 : pool_sum_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pool_sum_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdv : d < v) by lia.
  destruct (PreH28 v (conj Hdv PreH1)) as [Hlo Hhi].
  pose proof (Z.rem_small (Znth v anslist 0) 998244353 (conj Hlo Hhi)) as Hrem.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdv : d < v) by lia.
  destruct (PreH28 v (conj Hdv PreH1)) as [Hlo Hhi].
  pose proof (Z.rem_small (Znth v anslist 0) 998244353 (conj Hlo Hhi)) as Hrem.
  dump_pre_spatial.
  int_auto.
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
  assert (Hdv : d < v) by lia.
  destruct (PreH28 v (conj Hdv PreH1)) as [Hlo Hhi].
  pose proof (Z.rem_small (Znth v anslist 0) 998244353 (conj Hlo Hhi)) as Hrem.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdv : d < v) by lia.
  destruct (PreH28 v (conj Hdv PreH1)) as [Hlo Hhi].
  pose proof (Z.rem_small (Znth v anslist 0) 998244353 (conj Hlo Hhi)) as Hrem.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [| k IH]; intros x lo hi; simpl.
    - Exists (@nil Z). simpl.
      split_pure_spatial.
      + Intros_p Hlohi. cancel.
      + Intros_p Hlohi. split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l. Exists (a :: l). simpl. cancel.
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
  pose proof (maximum_value_bounds__solver_loop_plumbing vals PreH5) as Hmax.
  sep_apply_l_atomic (Hshape_full ans_pre (maxv_pre + 1)).
  Intros anslist.
  prop_apply_p (Int64Array.full_Zlength ans_pre (maxv_pre + 1) anslist).
  Intros_p Hlen.
  Exists anslist cnts_2 sums_2 squares_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold AnsExactPrefix; intros w Hw; lia);
      try (intros w Hw;
           pose proof (aggregate_entry_bounds__solver_loop_plumbing
                         vals freq cnts_2 sums_2 squares_2 maxv_pre w
                         PreH4 PreH6 PreH8 Hw);
           lia).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists anslist_2 cnts_2 sums_2 squares_2 1.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold PoolAggregate.
    replace (1 - 1) with 0 by lia.
    destruct (multiple_prefix_sum_step__solver_loop_plumbing cnts_2 d 0)
      as [Hc0 _].
    destruct (multiple_prefix_sum_step__solver_loop_plumbing sums_2 d 0)
      as [Hs0 _].
    destruct (multiple_prefix_sum_step__solver_loop_plumbing squares_2 d 0)
      as [Hq0 _].
    rewrite Hc0, Hs0, Hq0.
    rewrite Zmod_0_l.
    repeat split; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hv : 0 <= v <= maxv_pre) by lia.
  assert (Hcv : 0 <= Znth v cnts_2 0 <= 1000000000)
    by (pose proof (PreH27 v Hv); lia).
  assert (Hsv : 0 <= Znth v sums_2 0) by (pose proof (PreH27 v Hv); lia).
  assert (Hqv : 0 <= Znth v squares_2 0) by (pose proof (PreH27 v Hv); lia).
  pose proof (Z.rem_bound_pos (S + Znth v sums_2 0) 998244353
                ltac:(lia) ltac:(lia)) as HremS.
  pose proof (Z.rem_bound_pos (S2 + Znth v squares_2 0) 998244353
                ltac:(lia) ltac:(lia)) as HremS2.
  destruct PreH29 as [Hk [HS HS2]].
  destruct (multiple_prefix_sum_step__solver_loop_plumbing cnts_2 d t_2)
    as [_ Hcstep].
  destruct (multiple_prefix_sum_step__solver_loop_plumbing sums_2 d t_2)
    as [_ Hsstep].
  destruct (multiple_prefix_sum_step__solver_loop_plumbing squares_2 d t_2)
    as [_ Hqstep].
  specialize (Hcstep ltac:(lia)).
  specialize (Hsstep ltac:(lia)).
  specialize (Hqstep ltac:(lia)).
  rewrite <- PreH14 in Hcstep, Hsstep, Hqstep.
  Exists anslist_2 cnts_2 sums_2 squares_2 (t_2 + 1).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
    unfold PoolAggregate.
    replace (t_2 + 1 - 1) with t_2 by lia.
    rewrite Hcstep, Hsstep, Hqstep.
    rewrite <- Hk.
    rewrite (rem_eq_mod_nonneg__solver_loop_plumbing
               (S + Znth v sums_2 0) 998244353 ltac:(lia) ltac:(lia)).
    rewrite (rem_eq_mod_nonneg__solver_loop_plumbing
               (S2 + Znth v squares_2 0) 998244353 ltac:(lia) ltac:(lia)).
    rewrite HS, HS2.
    rewrite !Zplus_mod_idemp_l.
    repeat split; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (peel_state_init__sieve_math_core vals freq cnts_2 sums_2 squares_2 d t maxv_pre
           k S S2 retval v PreH5 PreH8 PreH9 PreH10 PreH11 PreH28 PreH14 PreH16 PreH17
           PreH4 PreH20 PreH32 PreH1).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH31; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH30; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9; lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
Qed.


Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists anslist_2 cnts_2 sums_2 squares_2 2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvlo : d < v) by nia.
  assert (Hva : 0 <= Znth v anslist_2 0 < 998244353)
    by (pose proof (PreH28 v ltac:(lia)); lia).
  pose proof (Z.rem_bound_pos (Znth v anslist_2 0) 998244353
                ltac:(lia) ltac:(lia)) as Hr.
  assert (Hrem : Z.rem (Znth v anslist_2 0) 998244353
                 = (exact_gcd_weight vals freq v) mod 998244353).
  { rewrite (rem_eq_mod_nonneg__solver_loop_plumbing
               (Znth v anslist_2 0) 998244353 ltac:(lia) ltac:(lia)).
    rewrite (PreH30 v ltac:(lia)).
    rewrite Zmod_mod. reflexivity. }
  pose proof (Z.rem_bound_pos
                (cur - Z.rem (Znth v anslist_2 0) 998244353 + 998244353)
                998244353 ltac:(lia) ltac:(lia)) as Hnew.
  Exists anslist_2 cnts_2 sums_2 squares_2 (t_2 + 1).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
    replace (t_2 + 1 - 1) with t_2 by lia.
    rewrite (rem_eq_mod_nonneg__solver_loop_plumbing
               (cur - Z.rem (Znth v anslist_2 0) 998244353 + 998244353)
               998244353 ltac:(lia) ltac:(lia)).
    rewrite Hrem.
    apply (peel_state_step__solver_loop_plumbing vals freq d t_2 v cur);
      [lia | exact PreH14 | exact PreH29].
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (ans_exact_prefix_step__sieve_math_core vals freq anslist_2 d t maxv_pre cur v
           PreH26
           (vals_in_bounds__sieve_math_core vals maxv_pre PreH8 PreH6)
           PreH11 PreH12 PreH13 PreH14 PreH1 PreH16 PreH29 PreH30).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec w_2 d) as [Heq | Hne].
  - subst w_2. rewrite Znth_replace_Znth_Same by lia. lia.
  - rewrite Znth_replace_Znth_Diff by lia. apply PreH28; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH27; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. exact PreH26.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_6 : solver_entail_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6; lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_6.
Qed.


Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  exact (solver_spec_final__sieve_math_core vals freq anslist maxv_pre d
           PreH2 PreH5 PreH7 PreH9 PreH1 PreH17).
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Int64Array.full_to_full_shape ans_pre (maxv_pre + 1) anslist).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed. 
