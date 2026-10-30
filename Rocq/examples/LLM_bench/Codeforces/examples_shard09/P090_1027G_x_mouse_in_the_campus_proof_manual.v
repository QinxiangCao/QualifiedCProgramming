From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P090_1027G_x_mouse_in_the_campus_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P090_1027G_x_mouse_in_the_campus_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.
Local Open Scope sac.

Lemma proof_of_mulmod_entail_wit_1_split_goal_1 : mulmod_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MulLoopState.
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite Z.add_0_l.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  reflexivity.
Qed.

Lemma proof_of_mulmod_entail_wit_1_split_goal_2 : mulmod_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos b0 modulus0 ltac:(lia) ltac:(lia)) as Hbrem.
  subst.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_1_split_goal_3 : mulmod_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos b_pre modulus_pre ltac:(lia) ltac:(lia)) as Hbrem.
  subst.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_1_split_goal_4 : mulmod_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos a_pre modulus_pre ltac:(lia) ltac:(lia)) as Harem.
  subst.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_1_split_goal_5 : mulmod_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos a_pre modulus_pre ltac:(lia) ltac:(lia)) as Harem.
  subst.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_1 : mulmod_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_mulmod_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_mulmod_entail_wit_2_1_split_goal_1 : mulmod_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  cbn [Z.pow] in *.
  rewrite unsigned_last_nbits_eq in * by (split; nia).
  rewrite Z.shiftr_div_pow2 by lia.
  cbn [Z.pow].
  unfold MulLoopState in *.
  replace 1 with (Z.ones 1) in PreH18 by reflexivity.
  rewrite Z.land_ones in PreH18 by lia.
  cbn [Z.ones Z.pow] in PreH18.
  pose proof (Z.mod_pos_bound b 2 ltac:(lia)) as Hbmod.
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hbdiv.
  replace (Z.pow_pos 2 1) with 2 in * by reflexivity.
  replace (r + a - modulus_pre + (a * 2 - modulus_pre) * (b / 2))
    with ((r + a * b) - modulus_pre * (1 + b / 2)) by nia.
  rewrite Zminus_mod.
  rewrite Zmult_mod.
  rewrite Z.mod_same by lia.
  cbn.
  rewrite Z.sub_0_r.
  rewrite Zmod_mod.
  exact PreH16.
Qed.

Lemma proof_of_mulmod_entail_wit_2_1_split_goal_2 : mulmod_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_1_split_goal_3 : mulmod_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_1_split_goal_4 : mulmod_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftl_mul_pow2 in * by lia.
  cbn [Z.pow] in *.
  rewrite unsigned_last_nbits_eq in * by (split; nia).
  replace (Z.pow_pos 2 1) with 2 in * by reflexivity.
  nia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_1 : mulmod_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_2_1_split_goal_4.
Qed.

Lemma proof_of_mulmod_entail_wit_2_2_split_goal_1 : mulmod_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  cbn [Z.pow] in *.
  rewrite unsigned_last_nbits_eq in * by (split; nia).
  rewrite Z.shiftr_div_pow2 by lia.
  cbn [Z.pow].
  unfold MulLoopState in *.
  replace 1 with (Z.ones 1) in PreH18 by reflexivity.
  rewrite Z.land_ones in PreH18 by lia.
  cbn [Z.ones Z.pow] in PreH18.
  pose proof (Z.mod_pos_bound b 2 ltac:(lia)) as Hbmod.
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hbdiv.
  replace (Z.pow_pos 2 1) with 2 in * by reflexivity.
  replace (r + a + (a * 2 - modulus_pre) * (b / 2))
    with ((r + a * b) - modulus_pre * (b / 2)) by nia.
  rewrite Zminus_mod.
  rewrite Zmult_mod.
  rewrite Z.mod_same by lia.
  cbn.
  rewrite Z.sub_0_r.
  rewrite Zmod_mod.
  exact PreH16.
Qed.

Lemma proof_of_mulmod_entail_wit_2_2_split_goal_2 : mulmod_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_2_split_goal_3 : mulmod_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_2_split_goal_4 : mulmod_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftl_mul_pow2 in * by lia.
  cbn [Z.pow] in *.
  rewrite unsigned_last_nbits_eq in * by (split; nia).
  replace (Z.pow_pos 2 1) with 2 in * by reflexivity.
  nia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_2 : mulmod_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_2_2_split_goal_4.
Qed.

Lemma proof_of_mulmod_entail_wit_2_3_split_goal_1 : mulmod_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  cbn [Z.pow] in *.
  rewrite unsigned_last_nbits_eq in * by (split; nia).
  rewrite Z.shiftr_div_pow2 by lia.
  cbn [Z.pow].
  unfold MulLoopState in *.
  replace 1 with (Z.ones 1) in PreH17 by reflexivity.
  rewrite Z.land_ones in PreH17 by lia.
  cbn [Z.ones Z.pow] in PreH17.
  pose proof (Z.mod_pos_bound b 2 ltac:(lia)) as Hbmod.
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hbdiv.
  replace (Z.pow_pos 2 1) with 2 in * by reflexivity.
  replace (r + (a * 2 - modulus_pre) * (b / 2))
    with ((r + a * b) - modulus_pre * (b / 2)) by nia.
  rewrite Zminus_mod.
  rewrite Zmult_mod.
  rewrite Z.mod_same by lia.
  cbn.
  rewrite Z.sub_0_r.
  rewrite Zmod_mod.
  exact PreH15.
Qed.

Lemma proof_of_mulmod_entail_wit_2_3_split_goal_2 : mulmod_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_3_split_goal_3 : mulmod_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_3_split_goal_4 : mulmod_entail_wit_2_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftl_mul_pow2 in * by lia.
  cbn [Z.pow] in *.
  rewrite unsigned_last_nbits_eq in * by (split; nia).
  replace (Z.pow_pos 2 1) with 2 in * by reflexivity.
  nia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_3 : mulmod_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_2_3_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_2_3_split_goal_4.
Qed.

Lemma proof_of_mulmod_entail_wit_2_4_split_goal_1 : mulmod_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  unfold MulLoopState in *.
  rewrite Z.shiftl_mul_pow2 by lia.
  simpl Z.pow.
  rewrite unsigned_last_nbits_eq by nia.
  rewrite Z.shiftr_div_pow2 by lia.
  simpl Z.pow.
  change (Z.pow_pos 2 1) with 2 in *.
  assert (Hbit : Z.land b 1 = b mod 2).
  {
    change (Z.land b (Z.ones 1) = b mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  assert (Hmod : b mod 2 = 1).
  { pose proof (Z.mod_pos_bound b 2 ltac:(lia)). lia. }
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hdecomp.
  replace ((r + a - modulus_pre + (a * 2) * (b / 2)) mod modulus_pre)
    with ((r + a * b - modulus_pre) mod modulus_pre) by (f_equal; nia).
  change ((r + a * b - modulus_pre) mod modulus_pre =
          (a_pre * b_pre) mod modulus_pre).
  rewrite <- Zminus_mod_idemp_r.
  rewrite Z_mod_same_full.
  rewrite Z.sub_0_r.
  exact PreH16.
Qed.

Lemma proof_of_mulmod_entail_wit_2_4_split_goal_2 : mulmod_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  simpl Z.pow.
  change (Z.pow_pos 2 1) with 2.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_4_split_goal_3 : mulmod_entail_wit_2_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.shiftr_nonneg.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_4_split_goal_4 : mulmod_entail_wit_2_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (unsigned_Lastnbits_range (Z.shiftl a 1) 64 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_4 : mulmod_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_2_4_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_2_4_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_2_4_split_goal_4.
Qed.

Lemma proof_of_mulmod_entail_wit_2_5_split_goal_1 : mulmod_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  unfold MulLoopState in *.
  rewrite Z.shiftl_mul_pow2 by lia.
  simpl Z.pow.
  rewrite unsigned_last_nbits_eq by nia.
  rewrite Z.shiftr_div_pow2 by lia.
  simpl Z.pow.
  change (Z.pow_pos 2 1) with 2 in *.
  assert (Hbit : Z.land b 1 = b mod 2).
  {
    change (Z.land b (Z.ones 1) = b mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  assert (Hmod : b mod 2 = 1).
  { pose proof (Z.mod_pos_bound b 2 ltac:(lia)). lia. }
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hdecomp.
  replace ((r + a + (a * 2) * (b / 2)) mod modulus_pre)
    with ((r + a * b) mod modulus_pre) by (f_equal; nia).
  exact PreH16.
Qed.

Lemma proof_of_mulmod_entail_wit_2_5_split_goal_2 : mulmod_entail_wit_2_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  simpl Z.pow.
  change (Z.pow_pos 2 1) with 2.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_5_split_goal_3 : mulmod_entail_wit_2_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.shiftr_nonneg.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_5_split_goal_4 : mulmod_entail_wit_2_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (unsigned_Lastnbits_range (Z.shiftl a 1) 64 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_5 : mulmod_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_2_5_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_2_5_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_2_5_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_2_5_split_goal_4.
Qed.

Lemma proof_of_mulmod_entail_wit_2_6_split_goal_1 : mulmod_entail_wit_2_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  unfold MulLoopState in *.
  rewrite Z.shiftl_mul_pow2 by lia.
  simpl Z.pow.
  rewrite unsigned_last_nbits_eq by nia.
  rewrite Z.shiftr_div_pow2 by lia.
  simpl Z.pow.
  change (Z.pow_pos 2 1) with 2 in *.
  assert (Hbit : Z.land b 1 = b mod 2).
  {
    change (Z.land b (Z.ones 1) = b mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  assert (Hmod : b mod 2 = 0).
  { lia. }
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hdecomp.
  replace ((r + (a * 2) * (b / 2)) mod modulus_pre)
    with ((r + a * b) mod modulus_pre) by (f_equal; nia).
  exact PreH15.
Qed.

Lemma proof_of_mulmod_entail_wit_2_6_split_goal_2 : mulmod_entail_wit_2_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  simpl Z.pow.
  change (Z.pow_pos 2 1) with 2.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_6_split_goal_3 : mulmod_entail_wit_2_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.shiftr_nonneg.
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_6_split_goal_4 : mulmod_entail_wit_2_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (unsigned_Lastnbits_range (Z.shiftl a 1) 64 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mulmod_entail_wit_2_6 : mulmod_entail_wit_2_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_entail_wit_2_6_split_goal_1.
  - Goal_apply proof_of_mulmod_entail_wit_2_6_split_goal_2.
  - Goal_apply proof_of_mulmod_entail_wit_2_6_split_goal_3.
  - Goal_apply proof_of_mulmod_entail_wit_2_6_split_goal_4.
Qed.

Lemma proof_of_mulmod_return_wit_1_split_goal_1 : mulmod_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 a0 b0.
  unfold MulLoopState in PreH14.
  subst b.
  rewrite Z.mul_0_r, Z.add_0_r in PreH14.
  rewrite Z.mod_small in PreH14 by lia.
  rewrite Z.rem_mod_nonneg by nia.
  exact PreH14.
Qed.

Lemma proof_of_mulmod_return_wit_1 : mulmod_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mulmod_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_powmod_entail_wit_1_split_goal_1 : powmod_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0.
  unfold PowLoopState.
  rewrite !Z.rem_mod_nonneg by lia.
  destruct (Z.eq_dec modulus_pre 1) as [Heq | Hneq].
  - subst modulus_pre.
    rewrite !Z.mod_1_r. reflexivity.
  - assert (Hone : 1 mod modulus_pre = 1).
    { apply Z.mod_small. lia. }
    rewrite Hone, Z.mul_1_l.
    apply pow_mod_base__powmod_loop; lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_split_goal_2 : powmod_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound 1 modulus_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_split_goal_3 : powmod_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound 1 modulus_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_split_goal_4 : powmod_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 base.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound b_pre modulus_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1_split_goal_5 : powmod_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst modulus0 base.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound b_pre modulus_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_1 : powmod_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_powmod_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_powmod_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_powmod_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_1 : powmod_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  rewrite !Z.rem_mod_nonneg by lia.
  eapply pow_loop_odd_step__powmod_loop; eauto; lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_2 : powmod_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  pose proof
    (Z.div_le_upper_bound e 2 e ltac:(lia) ltac:(nia)) as Hhalf_le.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1_split_goal_3 : powmod_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_1 : powmod_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_powmod_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_1 : powmod_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  rewrite !Z.rem_mod_nonneg by lia.
  eapply pow_loop_even_step__powmod_loop; eauto; lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_2 : powmod_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  pose proof
    (Z.div_le_upper_bound e 2 e ltac:(lia) ltac:(nia)) as Hhalf_le.
  lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2_split_goal_3 : powmod_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_powmod_entail_wit_2_2 : powmod_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_powmod_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_powmod_return_wit_1_split_goal_1 : powmod_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PowLoopState in PreH13.
  subst base. subst exponent. subst modulus0. subst e.
  rewrite Z.pow_0_r, Z.mul_1_r in PreH13.
  rewrite Z.mod_small in PreH13 by lia.
  rewrite Z.rem_mod_nonneg by lia.
  exact PreH13.
Qed.

Lemma proof_of_powmod_return_wit_1 : powmod_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_powmod_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gcd__entail_wit_1_split_goal_1 : gcd__entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_gcd__entail_wit_1 : gcd__entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcd__entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_gcd__entail_wit_2_split_goal_1 : gcd__entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  unfold GcdLoopState in *.
  etransitivity.
  - apply Z.gcd_comm.
  - rewrite (Z.gcd_rem a b PreH10).
    rewrite <- PreH9.
    apply Z.gcd_comm.
Qed.

Lemma proof_of_gcd__entail_wit_2_split_goal_2 : gcd__entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_nonneg a b PreH10 PreH5) as Hrem_nonneg.
  pose proof (Z.rem_bound_abs a b PreH10) as Hrem_bound.
  rewrite !Z.abs_eq in Hrem_bound by lia.
  lia.
Qed.

Lemma proof_of_gcd__entail_wit_2_split_goal_3 : gcd__entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_nonneg a b PreH10 PreH5) as Hrem_nonneg.
  lia.
Qed.

Lemma proof_of_gcd__entail_wit_2 : gcd__entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcd__entail_wit_2_split_goal_1.
  - Goal_apply proof_of_gcd__entail_wit_2_split_goal_2.
  - Goal_apply proof_of_gcd__entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_gcd__return_wit_1_split_goal_1 : gcd__return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GcdLoopState in *.
  subst b.
  rewrite Z.gcd_0_r in PreH9.
  rewrite Z.abs_eq in PreH9 by lia.
  assert (Hdiv : (Z.gcd a0 b0 | a0 + b0)).
  {
    apply Z.divide_add_r.
    - apply Z.gcd_divide_l.
    - apply Z.gcd_divide_r.
  }
  destruct (Z.eq_dec (a0 + b0) 0) as [Hzero | Hnonzero].
  - assert (Ha0 : a0 = 0) by lia.
    assert (Hb0 : b0 = 0) by lia.
    rewrite Ha0, Hb0 in PreH9.
    simpl in PreH9.
    lia.
  - assert (Z.gcd a0 b0 <= a0 + b0).
    {
      apply Z.divide_pos_le.
      - lia.
      - exact Hdiv.
    }
    lia.
Qed.

Lemma proof_of_gcd__return_wit_1_split_goal_2 : gcd__return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GcdLoopState in *.
  subst b.
  rewrite Z.gcd_0_r in PreH9.
  rewrite Z.abs_eq in PreH9 by lia.
  exact PreH9.
Qed.

Lemma proof_of_gcd__return_wit_1 : gcd__return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcd__return_wit_1_split_goal_1.
  - Goal_apply proof_of_gcd__return_wit_1_split_goal_2.
Qed.

Lemma proof_of_order_entail_wit_1_split_goal_1 : order_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply order_trial_init_ex.
  exact PreH6.
Qed.

Lemma proof_of_order_entail_wit_1_split_goal_2 : order_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (order_input_positive x0 modulus0 phi0 PreH6) as Hpositive.
  lia.
Qed.

Lemma proof_of_order_entail_wit_1_split_goal_3 : order_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (order_input_positive x0 modulus0 phi0 PreH6) as Hpositive.
  lia.
Qed.

Lemma proof_of_order_entail_wit_1_split_goal_4 : order_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OrderInput in PreH6.
  lia.
Qed.

Lemma proof_of_order_entail_wit_1 : order_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_order_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_order_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_order_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_order_entail_wit_2_split_goal_1 : order_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  apply order_trial_enter_factor_ex.
  - lia.
  - exact PreH14.
  - rewrite Z.rem_mod in PreH1 by lia.
    rewrite Z.sgn_pos in PreH1 by lia.
    rewrite !Z.abs_eq in PreH1 by lia.
    rewrite Z.mul_1_l in PreH1.
    exact PreH1.
Qed.

Lemma proof_of_order_entail_wit_2_split_goal_2 : order_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OrderTrialStateEx, OrderInput in PreH14.
  nia.
Qed.

Lemma proof_of_order_entail_wit_2 : order_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_order_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_order_entail_wit_3_split_goal_1 : order_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmod : t mod q = 0).
  { rewrite Z.rem_mod in PreH1 by lia.
    rewrite Z.sgn_pos in PreH1 by lia.
    rewrite !Z.abs_eq in PreH1 by lia.
    rewrite Z.mul_1_l in PreH1.
    exact PreH1. }
  rewrite Z.quot_div_nonneg by lia.
  eapply order_factor_step_div_ex; eauto.
  rewrite PreH2, PreH3, PreH4.
  exact PreH13.
Qed.

Lemma proof_of_order_entail_wit_3_split_goal_2 : order_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hmod : t mod q = 0).
  { rewrite Z.rem_mod in PreH1 by lia.
    rewrite Z.sgn_pos in PreH1 by lia.
    rewrite !Z.abs_eq in PreH1 by lia.
    rewrite Z.mul_1_l in PreH1.
    exact PreH1. }
  pose proof (order_factor_step_div_ex x_pre modulus_pre phi_pre q t ord
                PreH13 Hmod) as Hstate.
  unfold OrderFactorStateEx in Hstate.
  rewrite PreH4.
  tauto.
Qed.

Lemma proof_of_order_entail_wit_3_split_goal_3 : order_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hmod : t mod q = 0).
  { rewrite Z.rem_mod in PreH1 by lia.
    rewrite Z.sgn_pos in PreH1 by lia.
    rewrite !Z.abs_eq in PreH1 by lia.
    rewrite Z.mul_1_l in PreH1.
    exact PreH1. }
  pose proof (order_factor_step_div_ex x_pre modulus_pre phi_pre q t ord
                PreH13 Hmod) as Hstate.
  unfold OrderFactorStateEx in Hstate.
  tauto.
Qed.

Lemma proof_of_order_entail_wit_3 : order_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_order_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_order_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_order_entail_wit_4_split_goal_1 : order_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0. subst modulus0. subst phi0.
  eapply order_factor_completed_ex; eauto.
  rewrite Z.rem_mod in PreH1 by lia.
  rewrite Z.sgn_pos in PreH1 by lia.
  rewrite !Z.abs_eq in PreH1 by lia.
  rewrite Z.mul_1_l in PreH1.
  exact PreH1.
Qed.

Lemma proof_of_order_entail_wit_4 : order_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_order_entail_wit_5_split_goal_1 : order_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0. subst modulus0. subst phi0.
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  rewrite Z.rem_mod in PreH5 by lia.
  rewrite Z.sgn_pos in PreH5 by lia.
  rewrite !Z.abs_eq in PreH5 by lia.
  rewrite Z.mul_1_l in PreH5.
  apply order_strip_step_div_ex.
  - exact PreH17.
  - exact PreH5.
  - apply rem_one_implies_mod_one__order_entry_and_factorization.
    + lia.
    + congruence.
Qed.

Lemma proof_of_order_entail_wit_5_split_goal_2 : order_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst phi0.
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  rewrite Z.rem_mod in PreH5 by lia.
  rewrite Z.sgn_pos in PreH5 by lia.
  rewrite !Z.abs_eq in PreH5 by lia.
  rewrite Z.mul_1_l in PreH5.
  assert (Hpow : Z.pow x_pre (ord / q) mod modulus_pre = 1).
  { apply rem_one_implies_mod_one__order_entry_and_factorization; [lia | congruence]. }
  pose proof (order_strip_step_div_ex x_pre modulus_pre phi_pre q t ord
                PreH17 PreH5 Hpow) as Hstate.
  unfold OrderStripStateEx, OrderFactorStateEx in Hstate.
  destruct Hstate as [(_ & _ & _ & _ & _ & _ & [excess [Hcore _]]) _].
  unfold OrderCore in Hcore.
  destruct Hcore as (_ & _ & Hle & _).
  exact Hle.
Qed.

Lemma proof_of_order_entail_wit_5_split_goal_3 : order_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  rewrite Z.rem_mod in PreH5 by lia.
  rewrite Z.sgn_pos in PreH5 by lia.
  rewrite !Z.abs_eq in PreH5 by lia.
  rewrite Z.mul_1_l in PreH5.
  assert (Hpow : Z.pow x_pre (ord / q) mod modulus_pre = 1).
  { apply rem_one_implies_mod_one__order_entry_and_factorization; [lia | congruence]. }
  pose proof (order_strip_step_div_ex x_pre modulus_pre phi_pre q t ord
                PreH17 PreH5 Hpow) as Hstate.
  unfold OrderStripStateEx, OrderFactorStateEx in Hstate.
  destruct Hstate as [(_ & _ & _ & _ & _ & _ & [excess [Hcore _]]) _].
  unfold OrderCore in Hcore.
  destruct Hcore as (_ & Hpositive & _).
  exact Hpositive.
Qed.

Lemma proof_of_order_entail_wit_5 : order_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_order_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_order_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_order_entail_wit_6_1_split_goal_1 : order_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0.
  subst modulus0.
  subst phi0.
  eapply order_strip_exit_mod_ex; eauto.
  rewrite <- (Z.rem_mod_nonneg ord q) by lia.
  exact PreH1.
Qed.

Lemma proof_of_order_entail_wit_6_1 : order_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_order_entail_wit_6_2_split_goal_1 : order_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0; subst modulus0; subst phi0.
  eapply (order_strip_exit_power_ex x_pre modulus_pre phi_pre q t ord retval).
  - exact PreH17.
  - rewrite <- Z.rem_mod_nonneg by lia.
    exact PreH5.
  - assert (Hquot : ord ÷ q = ord / q) by (apply Z.quot_div_nonneg; lia).
    assert (Hremmod :
      Z.rem (Z.pow x_pre (ord ÷ q)) modulus_pre =
      Z.pow x_pre (ord ÷ q) mod modulus_pre).
    { apply rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits.
      - lia.
      - rewrite <- PreH2; exact PreH3. }
    rewrite <- Hquot, <- Hremmod.
    exact PreH2.
  - exact PreH1.
Qed.

Lemma proof_of_order_entail_wit_6_2 : order_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_order_entail_wit_6_3_split_goal_1 : order_entail_wit_6_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0; subst modulus0; subst phi0.
  eapply order_trial_skip_ex; eauto.
  intro Hmod.
  apply PreH1.
  rewrite Z.rem_mod_nonneg by lia.
  exact Hmod.
Qed.

Lemma proof_of_order_entail_wit_6_3_split_goal_2 : order_entail_wit_6_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH14 as (Hinput & _).
  unfold OrderInput in Hinput.
  nia.
Qed.

Lemma proof_of_order_entail_wit_6_3 : order_entail_wit_6_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_6_3_split_goal_1.
  - Goal_apply proof_of_order_entail_wit_6_3_split_goal_2.
Qed.

Lemma proof_of_order_entail_wit_7_split_goal_1 : order_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0; subst modulus0; subst phi0.
  eapply order_trial_enter_final_ex.
  - exact PreH8.
  - lia.
  - lia.
  - exact PreH14.
Qed.

Lemma proof_of_order_entail_wit_7 : order_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_order_entail_wit_8_split_goal_1 : order_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst x0; subst modulus0; subst phi0.
  assert (Hmod : ord mod t = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH5. }
  assert (Hquot : ord ÷ t = ord / t) by (apply Z.quot_div_nonneg; lia).
  assert (Hremmod :
    Z.rem (Z.pow x_pre (ord ÷ t)) modulus_pre =
    Z.pow x_pre (ord ÷ t) mod modulus_pre).
  { apply rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits.
    - lia.
    - rewrite <- PreH2, PreH1; lia. }
  assert (Hpow : Z.pow x_pre (ord / t) mod modulus_pre = 1).
  { rewrite <- Hquot, <- Hremmod, <- PreH2, PreH1; reflexivity. }
  pose proof (order_final_step_div_ex x_pre modulus_pre phi_pre t ord
                PreH15 Hmod Hpow) as Hstate.
  rewrite Hquot.
  exact Hstate.
Qed.

Lemma proof_of_order_entail_wit_8_split_goal_2 : order_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst phi0.
  assert (Hmod : ord mod t = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH5. }
  assert (Hquot : ord ÷ t = ord / t) by (apply Z.quot_div_nonneg; lia).
  assert (Hremmod :
    Z.rem (Z.pow x_pre (ord ÷ t)) modulus_pre =
    Z.pow x_pre (ord ÷ t) mod modulus_pre).
  { apply rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits.
    - lia.
    - rewrite <- PreH2, PreH1; lia. }
  assert (Hpow : Z.pow x_pre (ord / t) mod modulus_pre = 1).
  { rewrite <- Hquot, <- Hremmod, <- PreH2, PreH1; reflexivity. }
  pose proof (order_final_step_div_ex x_pre modulus_pre phi_pre t ord
                PreH15 Hmod Hpow) as Hstate.
  rewrite Hquot.
  unfold OrderFinalStateEx, OrderCore in Hstate.
  destruct Hstate as (_ & _ & excess & Hcore & _).
  destruct Hcore as (_ & _ & Hle & _).
  exact Hle.
Qed.

Lemma proof_of_order_entail_wit_8_split_goal_3 : order_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmod : ord mod t = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH5. }
  assert (Hquot : ord ÷ t = ord / t) by (apply Z.quot_div_nonneg; lia).
  assert (Hremmod :
    Z.rem (Z.pow x_pre (ord ÷ t)) modulus_pre =
    Z.pow x_pre (ord ÷ t) mod modulus_pre).
  { apply rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits.
    - lia.
    - rewrite <- PreH2, PreH1; lia. }
  assert (Hpow : Z.pow x_pre (ord / t) mod modulus_pre = 1).
  { rewrite <- Hquot, <- Hremmod, <- PreH2, PreH1; reflexivity. }
  pose proof (order_final_step_div_ex x_pre modulus_pre phi_pre t ord
                PreH15 Hmod Hpow) as Hstate.
  rewrite Hquot.
  unfold OrderFinalStateEx, OrderCore in Hstate.
  destruct Hstate as (_ & _ & excess & Hcore & _).
  destruct Hcore as (_ & Hpos & _).
  exact Hpos.
Qed.

Lemma proof_of_order_entail_wit_8 : order_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_order_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_order_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_order_return_wit_1_split_goal_1 : order_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply order_final_exit_mod_ex; eauto.
  rewrite <- Z.rem_mod_nonneg by lia.
  exact PreH1.
Qed.

Lemma proof_of_order_return_wit_1 : order_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_order_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_order_return_wit_2_split_goal_1 : order_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply order_final_exit_power_guard_ex; eauto.
  - rewrite <- Z.rem_mod_nonneg by lia.
    exact PreH5.
  - assert (Hquot : ord ÷ t = ord / t).
    { apply Z.quot_div_nonneg; lia. }
    rewrite <- Hquot.
    set (a := x_pre ^ (ord ÷ t)) in *.
    assert (Hremmod : Z.rem a modulus_pre = a mod modulus_pre).
    { destruct (Z_le_gt_dec 0 a) as [Ha | Ha].
      - apply Z.rem_mod_nonneg; lia.
      - assert (Hremnonpos : Z.rem a modulus_pre <= 0).
        { apply Z.rem_nonpos; lia. }
        assert (Hremzero : Z.rem a modulus_pre = 0) by lia.
        assert (Hdiv : (modulus_pre | a)).
        { apply (proj1 (Z.rem_divide a modulus_pre ltac:(lia))).
          exact Hremzero. }
        rewrite Hremzero.
        symmetry.
        apply (proj2 (Z.mod_divide a modulus_pre ltac:(lia))).
        exact Hdiv. }
    rewrite <- Hremmod.
    exact PreH1.
Qed.

Lemma proof_of_order_return_wit_2 : order_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_order_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_order_return_wit_3_split_goal_1 : order_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply order_trial_exit_bounded_ex; eauto.
Qed.

Lemma proof_of_order_return_wit_3 : order_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_order_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_order_return_wit_4_split_goal_1 : order_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  unfold OrderInput, OrderResult, Ord in *.
  simpl in *.
  lia.
Qed.

Lemma proof_of_order_return_wit_4 : order_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_order_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_order_partial_solve_wit_1_pure_split_goal_1 : order_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdiv : 0 <= ord / q).
  { apply Z.div_pos; lia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  exact Hdiv.
Qed.

Lemma proof_of_order_partial_solve_wit_1_pure_split_goal_2 : order_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OrderStripStateEx, OrderFactorStateEx, OrderCore, OrderInput in PreH25.
  assert (Hdiv : ord / q <= ord).
  { apply Z.div_le_upper_bound; nia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  intuition lia.
Qed.

Lemma proof_of_order_partial_solve_wit_1_pure : order_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_order_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_order_partial_solve_wit_2_pure_split_goal_1 : order_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdiv : 0 <= ord / t).
  { apply Z.div_pos; lia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  exact Hdiv.
Qed.

Lemma proof_of_order_partial_solve_wit_2_pure_split_goal_2 : order_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OrderFinalStateEx, OrderCore, OrderInput in PreH21.
  assert (Hdiv : ord / t <= ord).
  { apply Z.div_le_upper_bound; nia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  intuition lia.
Qed.

Lemma proof_of_order_partial_solve_wit_2_pure : order_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_order_partial_solve_wit_2_pure_split_goal_2.
Qed.

Lemma proof_of_walk_safety_wit_10_split_goal_1 : walk_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH8 as (_ & _ & Hpk & _).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_walk_safety_wit_10 : walk_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_safety_wit_10_split_goal_1.
Qed.

Lemma proof_of_walk_entail_wit_1_split_goal_1 : walk_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply incoming_walk_suffix_zero_call_budget; eauto; lia.
Qed.

Lemma proof_of_walk_entail_wit_1_split_goal_2 : walk_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply prefix_choice_zero_extend; eauto; lia.
Qed.

Lemma proof_of_walk_entail_wit_1 : walk_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_walk_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_walk_entail_wit_2_split_goal_1 : walk_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply walk_pending_after_zero; eauto; lia.
Qed.

Lemma proof_of_walk_entail_wit_2 : walk_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_walk_entail_wit_3_split_goal_1 : walk_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i_pre - 0) with i_pre by lia.
  apply
    (walk_exponent_init_from_table
       m (Znth i_pre pr_values 0) pr_values pe_values i_pre).
  - unfold WalkGlobalBounds in PreH5.
    lia.
  - exact PreH8.
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_walk_entail_wit_3_split_goal_2 : walk_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  f_equal.
  lia.
Qed.

Lemma proof_of_walk_entail_wit_3_split_goal_3 : walk_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (valid_table_exponent_positive
       m pr_values pe_values i_pre PreH8 ltac:(lia)) as Hpositive.
  lia.
Qed.

Lemma proof_of_walk_entail_wit_3 : walk_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_walk_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_walk_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_walk_entail_wit_4_1_split_goal_1 : walk_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst e.
  replace (i_pre - 0) with i_pre in PreH2 by lia.
  pose proof (walk_exponent_step_first_from_table
    m p (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre
    ltac:(unfold WalkGlobalBounds in PreH11; lia)
    PreH14 ltac:(lia) PreH9 eq_refl PreH10) as Hstep.
  destruct Hstep as [Hstate [Hpk [Hph [Hpk_bounds Hph_bounds]]]].
  pose proof Hstate as Hstate_bounds.
  unfold WalkExponentState in Hstate_bounds.
  destruct Hstate_bounds as [_ [_ [Hproduct_bounds _]]].
  rewrite !unsigned_last_nbits_eq by lia.
  rewrite Z.rem_mod_nonneg by
    (unfold WalkGlobalBounds in PreH11; lia).
  pose proof (prefix_choice_selected _ _ _ _ _ _ _ PreH15) as Hselected.
  exact (prime_power_consumer_order_input
    m x_value p 1 (pk * p) (p - 1) d_pre
    pr_values pe_values i_pre PreH14 Hselected ltac:(lia)
    PreH9 ltac:(lia) PreH11 Hpk Hph).
Qed.

Lemma proof_of_walk_entail_wit_4_1_split_goal_2 : walk_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst e.
  pose proof (walk_exponent_step_first_from_table
    m p (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre
    ltac:(unfold WalkGlobalBounds in PreH11; lia)
    PreH14 ltac:(lia) PreH9 eq_refl PreH10) as Hstep.
  destruct Hstep as [Hstate [Hpk [Hph [Hpk_bounds Hph_bounds]]]].
  rewrite !unsigned_last_nbits_eq by lia.
  exact Hstate.
Qed.

Lemma proof_of_walk_entail_wit_4_1_split_goal_3 : walk_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply valid_table_exponent_positive; eauto; lia.
Qed.

Lemma proof_of_walk_entail_wit_4_1 : walk_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_walk_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_walk_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_walk_entail_wit_4_2_split_goal_1 : walk_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i_pre - 0) with i_pre in PreH2 by lia.
  pose proof (walk_exponent_step_later_from_table
    m p e (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre
    ltac:(unfold WalkGlobalBounds in PreH11; lia)
    PreH14 ltac:(lia) PreH9 eq_refl ltac:(lia) ltac:(lia) PreH10) as Hstep.
  destruct Hstep as [Hstate [Hpk [Hph [Hpk_bounds Hph_bounds]]]].
  pose proof Hstate as Hstate_bounds.
  unfold WalkExponentState in Hstate_bounds.
  destruct Hstate_bounds as [_ [_ [Hproduct_bounds _]]].
  rewrite !unsigned_last_nbits_eq by lia.
  rewrite Z.rem_mod_nonneg by
    (unfold WalkGlobalBounds in PreH11; lia).
  pose proof (prefix_choice_selected _ _ _ _ _ _ _ PreH15) as Hselected.
  exact (prime_power_consumer_order_input
    m x_value p e (pk * p) (ph * p) d_pre
    pr_values pe_values i_pre PreH14 Hselected ltac:(lia)
    PreH9 ltac:(lia) PreH11 Hpk Hph).
Qed.

Lemma proof_of_walk_entail_wit_4_2_split_goal_2 : walk_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i_pre - 0) with i_pre in PreH2 by lia.
  pose proof (walk_exponent_step_later_from_table
    m p e (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre
    ltac:(unfold WalkGlobalBounds in PreH11; lia)
    PreH14 ltac:(lia) PreH9 eq_refl ltac:(lia) ltac:(lia) PreH10) as Hstep.
  destruct Hstep as [Hstate [Hpk [Hph [Hpk_bounds Hph_bounds]]]].
  rewrite !unsigned_last_nbits_eq by lia.
  exact Hstate.
Qed.

Lemma proof_of_walk_entail_wit_4_2_split_goal_3 : walk_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i_pre - 0) with i_pre in PreH2 by lia.
  exact PreH2.
Qed.

Lemma proof_of_walk_entail_wit_4_2 : walk_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_walk_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_walk_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_walk_entail_wit_5_split_goal_1 : walk_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (walk_exponent_ready_for_transition
    m p e (Znth i_pre pe_values 0) pk ph ltac:(lia) PreH12)
    as [Hpk [Hph _]].
  rewrite Hpk, PreH11.
  exact (walk_pending_recursive_call_budget
    pr_values pe_values m x_value i_pre d_pre before current_2 e
    ltac:(lia) PreH19).
Qed.

Lemma proof_of_walk_entail_wit_5_split_goal_2 : walk_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH4 as [Ho [Hretval _]].
  rewrite Z.rem_mod_nonneg in Ho by
    (unfold OrderInput in PreH13; unfold WalkGlobalBounds in PreH14; lia).
  pose proof (walk_exponent_state_consumer_transition
    m x_value p e pk ph retval retval_2 d_pre phi_pre ord_pre
    pr_values pe_values i_pre PreH17 PreH18 ltac:(lia) PreH11
    ltac:(lia) PreH14 PreH12 Ho PreH1) as Htransition.
  destruct Htransition as [Hinput [Hprime [Hprefix Hbounds]]].
  assert (Hretval2 : 0 < retval_2).
  { rewrite PreH1.
    pose proof (Z.gcd_nonneg ord_pre retval).
    assert (Z.gcd ord_pre retval <> 0).
    { intro Hz. apply Z.gcd_eq_0 in Hz. lia. }
    lia. }
  assert (Hquot : ord_pre ÷ retval_2 = ord_pre / retval_2).
  { apply Z.quot_div_nonneg; lia. }
  rewrite Hquot.
  exact Hprefix.
Qed.

Lemma proof_of_walk_entail_wit_5_split_goal_3 : walk_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH4 as [Ho [Hretval _]].
  rewrite Z.rem_mod_nonneg in Ho by
    (unfold OrderInput in PreH13; unfold WalkGlobalBounds in PreH14; lia).
  pose proof (walk_exponent_state_consumer_transition
    m x_value p e pk ph retval retval_2 d_pre phi_pre ord_pre
    pr_values pe_values i_pre PreH17 PreH18 ltac:(lia) PreH11
    ltac:(lia) PreH14 PreH12 Ho PreH1) as Htransition.
  destruct Htransition as [Hinput [Hprime [Hprefix Hbounds]]].
  assert (Hretval2 : 0 < retval_2).
  { rewrite PreH1.
    pose proof (Z.gcd_nonneg ord_pre retval).
    assert (Z.gcd ord_pre retval <> 0).
    { intro Hz. apply Z.gcd_eq_0 in Hz. lia. }
    lia. }
  assert (Hquot : ord_pre ÷ retval_2 = ord_pre / retval_2).
  { apply Z.quot_div_nonneg; lia. }
  rewrite Hquot.
  exact Hprime.
Qed.

Lemma proof_of_walk_entail_wit_5_split_goal_4 : walk_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH4 as [Ho [Hretval _]].
  rewrite Z.rem_mod_nonneg in Ho by
    (unfold OrderInput in PreH13; unfold WalkGlobalBounds in PreH14; lia).
  pose proof (walk_exponent_state_consumer_transition
    m x_value p e pk ph retval retval_2 d_pre phi_pre ord_pre
    pr_values pe_values i_pre PreH17 PreH18 ltac:(lia) PreH11
    ltac:(lia) PreH14 PreH12 Ho PreH1) as Htransition.
  destruct Htransition as [Hinput [Hprime [Hprefix Hbounds]]].
  assert (Hretval2 : 0 < retval_2).
  { rewrite PreH1.
    pose proof (Z.gcd_nonneg ord_pre retval).
    assert (Z.gcd ord_pre retval <> 0).
    { intro Hz. apply Z.gcd_eq_0 in Hz. lia. }
    lia. }
  assert (Hquot : ord_pre ÷ retval_2 = ord_pre / retval_2).
  { apply Z.quot_div_nonneg; lia. }
  rewrite Hquot.
  exact Hbounds.
Qed.

Lemma proof_of_walk_entail_wit_5_split_goal_5 : walk_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH4 as [_ [Hretval _]].
  rewrite PreH1.
  pose proof (Z.gcd_nonneg ord_pre retval).
  assert (Z.gcd ord_pre retval <> 0).
  { intro Hz. apply Z.gcd_eq_0 in Hz. lia. }
  lia.
Qed.

Lemma proof_of_walk_entail_wit_5 : walk_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_walk_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_walk_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_walk_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_walk_entail_wit_5_split_goal_5.
Qed.

Lemma proof_of_walk_entail_wit_6_split_goal_1 : walk_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WalkGlobalBounds in PreH9.
  destruct PreH9 as [[Hm_lower Hm_upper] [Hx_bounds Hxm]].
  unfold WalkMachineBounds in PreH15.
  destruct PreH15 as [Hdpk_bounds _].
  destruct PreH14 as
    [Hp_bounds [He_bounds [Hpk_bounds [Hph_bounds [Hpk Hph]]]]].
  replace (e + 1 - 1) with e in Hpk by lia.
  pose proof (Z.pow_gt_lin_r p e ltac:(lia) ltac:(lia)) as He_power.
  assert (Hdwrap : unsigned_last_nbits (d_pre * pk) 64 = d_pre * pk).
  { apply unsigned_last_nbits_eq; lia. }
  assert (Hewrap : unsigned_last_nbits (e + 1) 64 = e + 1).
  { apply unsigned_last_nbits_eq.
    change (0 <= e + 1 < 18446744073709551616).
    rewrite Hpk in Hpk_bounds. lia. }
  rewrite Hdwrap, Hewrap.
  rewrite Hpk, PreH7.
  eapply walk_recursive_return_continuation; eauto; lia.
Qed.

Lemma proof_of_walk_entail_wit_6_split_goal_2 : walk_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH14 as Hstate.
  destruct PreH14 as
    [Hp_bounds [He_bounds [Hpk_bounds [Hph_bounds [Hpk Hph]]]]].
  replace (e + 1 - 1) with e in Hpk by lia.
  unfold WalkGlobalBounds in PreH9.
  destruct PreH9 as [[Hm_lower Hm_upper] [Hx_bounds Hxm]].
  pose proof (Z.pow_gt_lin_r p e ltac:(lia) ltac:(lia)) as He_power.
  rewrite unsigned_last_nbits_eq by lia.
  exact Hstate.
Qed.

Lemma proof_of_walk_entail_wit_6_split_goal_3 : walk_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH14 as
    [Hp_bounds [He_bounds [Hpk_bounds [Hph_bounds [Hpk Hph]]]]].
  replace (e + 1 - 1) with e in Hpk by lia.
  unfold WalkGlobalBounds in PreH9.
  destruct PreH9 as [[Hm_lower Hm_upper] [Hx_bounds Hxm]].
  pose proof (Z.pow_gt_lin_r p e ltac:(lia) ltac:(lia)) as He_power.
  rewrite unsigned_last_nbits_eq by lia.
  lia.
Qed.

Lemma proof_of_walk_entail_wit_6_split_goal_4 : walk_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH14 as
    [Hp_bounds [He_bounds [Hpk_bounds [Hph_bounds [Hpk Hph]]]]].
  replace (e + 1 - 1) with e in Hpk by lia.
  unfold WalkGlobalBounds in PreH9.
  destruct PreH9 as [[Hm_lower Hm_upper] [Hx_bounds Hxm]].
  pose proof (Z.pow_gt_lin_r p e ltac:(lia) ltac:(lia)) as He_power.
  rewrite unsigned_last_nbits_eq by lia.
  lia.
Qed.

Lemma proof_of_walk_entail_wit_6 : walk_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_walk_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_walk_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_walk_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_walk_return_wit_1_split_goal_1 : walk_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i_pre.
  rewrite (prefix_choice_terminal_walk_value
             pr_values pe_values x_value factor_count d_pre phi_pre ord_pre
             PreH11) by lia.
  rewrite (prefix_choice_terminal_walk_value
             pr_values pe_values x_value factor_count d_pre phi_pre ord_pre
             PreH11) in PreH12 by lia.
  unfold WalkBudget in PreH12.
  unfold WalkGlobalBounds in PreH7.
  unfold WalkMachineBounds in PreH8.
  destruct PreH12 as (Hbefore & Hwork & Hsum).
  destruct PreH7 as ((Hmlo & Hmhi) & Hx & Hgcdx).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hrange :
      0 <= before + phi_pre / ord_pre < 18446744073709551616) by lia.
  rewrite unsigned_last_nbits_eq by
      (change (2 ^ 64) with 18446744073709551616; exact Hrange).
  reflexivity.
Qed.

Lemma proof_of_walk_return_wit_1 : walk_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_walk_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_walk_return_wit_2_split_goal_1 : walk_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i_pre.
  pose proof (prefix_choice_positive
                pr_values pe_values x_value factor_count d_pre phi_pre ord_pre
                PreH11) as (Hd & _).
  assert (d_pre = 1) as Hd1 by lia.
  rewrite (walk_suffix_at_terminal pr_values pe_values x_value factor_count d_pre)
    by lia.
  subst d_pre.
  unfold CycleTerm.
  simpl.
  lia.
Qed.

Lemma proof_of_walk_return_wit_2 : walk_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_walk_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_walk_return_wit_3_split_goal_1 : walk_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (walk_pending_terminal
           pr_values pe_values m x_value i_pre d_pre before current e PreH15).
  replace (i_pre - 0) with i_pre in PreH1 by lia.
  lia.
Qed.

Lemma proof_of_walk_return_wit_3 : walk_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_walk_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_walk_partial_solve_wit_4_pure_split_goal_1 : walk_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WalkExponentState in PreH30.
  unfold WalkGlobalBounds in PreH32.
  destruct PreH30 as (Hp & He & Hpk & Hph & Hpkpow & Hphphi).
  destruct PreH32 as (Hm & Hx & Hgcd).
  destruct Hpk as (Hpklo & Hpkhi).
  destruct Hm as (Hmlo & Hmhi).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_walk_partial_solve_wit_4_pure : walk_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_walk_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_walk_partial_solve_wit_5_pure_split_goal_1 : walk_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WalkMachineBounds in PreH36.
  unfold WalkGlobalBounds in PreH35.
  destruct PreH36 as (Hd & Hphi & Hord).
  destruct PreH35 as (Hm & Hx & Hgcd).
  destruct Hord as (Hordlo & Hordhi).
  destruct Hm as (Hmlo & Hmhi).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_walk_partial_solve_wit_5_pure_split_goal_2 : walk_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OrderResult in PreH25.
  unfold OrderInput in PreH34.
  unfold WalkExponentState in PreH33.
  unfold WalkGlobalBounds in PreH35.
  destruct PreH25 as (Hretval & Hretpos & Hretdiv & Hretpow).
  destruct PreH34 as (Hpk & Hphi & Hgcd & Hphibound & Hord & Horddiv & Hpow).
  destruct PreH33 as (Hp & He & Hpkbound & Hphbound & Hpkpow & Hphphi).
  destruct PreH35 as (Hm & Hx & Hgcd_global).
  destruct Hpkbound as (Hpklo & Hpkhi).
  destruct Hm as (Hmlo & Hmhi).
  destruct Hphibound as (Hphilo & Hphihi).
  assert (Hretlephi : retval <= ph).
  {
    rewrite Hretval.
    eapply Z.divide_pos_le; [exact Hphilo | exact Horddiv].
  }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_walk_partial_solve_wit_5_pure : walk_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_walk_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_walk_partial_solve_wit_6_pure_split_goal_1 : walk_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH41 as Hbounds.
  unfold WalkGlobalBounds in PreH35.
  unfold WalkMachineBounds in PreH41.
  destruct PreH41 as [Hd [Hphi Hord]].
  rewrite !unsigned_last_nbits_eq by lia.
  dump_pre_spatial.
  exact Hbounds.
Qed.

Lemma proof_of_walk_partial_solve_wit_6_pure_split_goal_2 : walk_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WalkGlobalBounds in PreH35.
  unfold WalkMachineBounds in PreH41.
  destruct PreH41 as [Hd [Hphi Hord]].
  rewrite unsigned_last_nbits_eq by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_walk_partial_solve_wit_6_pure_split_goal_3 : walk_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WalkGlobalBounds in PreH35.
  unfold WalkMachineBounds in PreH41.
  destruct PreH41 as [Hd [Hphi Hord]].
  rewrite !unsigned_last_nbits_eq by lia.
  dump_pre_spatial.
  exact PreH43.
Qed.

Lemma proof_of_walk_partial_solve_wit_6_pure_split_goal_4 : walk_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WalkGlobalBounds in PreH35.
  unfold WalkMachineBounds in PreH41.
  destruct PreH41 as [Hd [Hphi Hord]].
  rewrite unsigned_last_nbits_eq by lia.
  dump_pre_spatial.
  exact PreH44.
Qed.

Lemma proof_of_walk_partial_solve_wit_6_pure : walk_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_walk_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_walk_partial_solve_wit_6_pure_split_goal_2.
  - Goal_apply proof_of_walk_partial_solve_wit_6_pure_split_goal_3.
  - Goal_apply proof_of_walk_partial_solve_wit_6_pure_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply factor_machine_trial_init.
  - lia.
  - unfold FactorInputLimit; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdiv : remainder mod p = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH1. }
  pose proof
    (factor_machine_enter_prime
      m_pre p remainder pr_values_2 pe_values_2 PreH16 PreH2 Hdiv)
    as Hfactor_start.
  pose proof Hfactor_start as Hfactor_bounds.
  unfold FactorMachineAtPrime, FactorCandidateGuardLimit in Hfactor_bounds.
  destruct Hfactor_bounds as (_ & _ & Hpbound).
  Exists remainder 0 pe_values_2 pr_values_2 factor_count_2.
  sep_apply_l_atomic
    (UInt64Array.seg_split_to_seg (&("pe")) 0 factor_count_2
      (factor_count_2 + 1) (pe_values_2 ++ (cons 0 (@nil Z)))).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic
      (UInt64Array.seg_split_to_seg (&("pr")) 0 factor_count_2
        (factor_count_2 + 1) (pr_values_2 ++ (cons p (@nil Z)))).
    + dump_pre_spatial; lia.
    + replace (factor_count_2 - 0) with factor_count_2 by lia.
      replace (factor_count_2 + 1 - 0) with (factor_count_2 + 1) by lia.
      replace (sublist 0 factor_count_2
        (pe_values_2 ++ (cons 0 (@nil Z))))
        with pe_values_2.
      2: { symmetry; rewrite <- PreH13; apply sublist_app_exact1. }
      replace
        (sublist factor_count_2 (factor_count_2 + 1)
          (pe_values_2 ++ (cons 0 (@nil Z))))
        with (cons 0 (@nil Z)).
      2: {
        symmetry.
        rewrite (sublist_split_app_r factor_count_2
          (factor_count_2 + 1) factor_count_2 pe_values_2
          (cons 0 (@nil Z)));
          try lia.
        replace (factor_count_2 - factor_count_2) with 0 by lia.
        replace (factor_count_2 + 1 - factor_count_2) with 1 by lia.
        reflexivity.
      }
      replace (sublist 0 factor_count_2
        (pr_values_2 ++ (cons p (@nil Z))))
        with pr_values_2.
      2: { symmetry; rewrite <- PreH12; apply sublist_app_exact1. }
      replace
        (sublist factor_count_2 (factor_count_2 + 1)
          (pr_values_2 ++ (cons p (@nil Z))))
        with (cons p (@nil Z)).
      2: {
        symmetry.
        rewrite (sublist_split_app_r factor_count_2
          (factor_count_2 + 1) factor_count_2 pr_values_2
          (cons p (@nil Z)));
          try lia.
        replace (factor_count_2 - factor_count_2) with 0 by lia.
        replace (factor_count_2 + 1 - factor_count_2) with 1 by lia.
        reflexivity.
      }
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH15 as Hfactor_components.
  unfold FactorMachineAtPrime, StrictFactorAtPrime in Hfactor_components.
  destruct Hfactor_components as
    ((_ & Hprime & _ & _ & _ & Hremainder_bounds) & _ & _).
  destruct Hprime as [Hp_positive _].
  assert (Hdiv : remainder mod p = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH1. }
  assert (Hdivision : remainder = p * (remainder / p)).
  {
    pose proof (Z_div_mod_eq_full remainder p) as Hdecompose.
    nia.
  }
  pose proof
    (factor_machine_divide_step
      m_pre p original_remainder_2 remainder (remainder / p)
      exponent_2 pr_values_2 pe_values_2 PreH15 Hdivision)
    as Hfactor_next.
  pose proof
    (factor_machine_active_exponent_bounds
      m_pre p original_remainder_2 (remainder / p) (exponent_2 + 1)
      pr_values_2 pe_values_2 Hfactor_next)
    as Hexponent_next.
  rewrite Z.quot_div_nonneg by lia.
  Exists original_remainder_2 (exponent_2 + 1)
    pe_values_2 pr_values_2 factor_count_2.
  replace (factor_count_2 - factor_count_2) with 0 by lia.
  replace (Znth 0 (cons exponent_2 (@nil Z)) 0) with exponent_2
    by reflexivity.
  rewrite unsigned_last_nbits_eq by
    (split; [lia | change (exponent_2 + 1 < 18446744073709551616); lia]).
  replace
    (replace_Znth 0 (exponent_2 + 1) (cons exponent_2 (@nil Z)))
    with (cons (exponent_2 + 1) (@nil Z)).
  2: {
    unfold replace_Znth.
    reflexivity.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH15 as Hstate_bounds.
  unfold FactorMachineAtPrime, StrictFactorAtPrime in Hstate_bounds.
  destruct Hstate_bounds as ((_ & _ & _ & _ & _ & Hbounds) & _ & _).
  assert (Hnotdiv : remainder mod p <> 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH1. }
  eapply factor_machine_finish_prime; eauto.
  rewrite PreH11; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH15 as Hstate.
  unfold FactorMachineAtPrime, StrictFactorAtPrime, StrictFactorPrefix,
    FactorPrefix in Hstate.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH15 as Hstate.
  unfold FactorMachineAtPrime, StrictFactorAtPrime in Hstate.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_5 : solver_entail_wit_4_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_6 : solver_entail_wit_4_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH15 as Hstate.
  unfold FactorMachineAtPrime in Hstate.
  destruct Hstate as (Hfactor & Hlimit & Hcandidate).
  unfold StrictFactorAtPrime in Hfactor.
  destruct Hfactor as (Hstrict & _).
  pose proof
    (strict_factor_prefix_length_lt_47
      m_pre p original_remainder pr_values_2 pe_values_2 Hstrict PreH3)
    as Hlength.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnotdiv : remainder mod p <> 0).
  { rewrite <- Z.rem_mod_nonneg by lia; exact PreH1. }
  eapply factor_machine_trial_skip; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH16 as [Htrial Hmachine].
  destruct (strict_trial_finalize_after_square_exit
    m_pre p remainder pr_values_2 pe_values_2
    Htrial PreH4 PreH2)
    as [final_pr [final_pe [Hvalid Hcases]]].
  destruct Hcases as [[Hone [Hpr Hpe]] | [Hgt [Hpr Hpe]]].
  - lia.
  - subst final_pr final_pe. exact Hvalid.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
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
  destruct PreH16 as [Htrial Hmachine].
  destruct (strict_trial_finalize_after_square_exit
    m_pre p remainder pr_values_2 pe_values_2
    Htrial PreH4 PreH2)
    as [final_pr [final_pe [Hvalid Hcases]]].
  destruct Hcases as [[Hone [Hpr Hpe]] | [Hgt [Hpr Hpe]]].
  - subst remainder final_pr final_pe. exact Hvalid.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (valid_factor_table_initial_walk_budget
    m_pre x_pre pr_values_2 pe_values_2 PreH10) as Hbudget.
  unfold WalkBudget in Hbudget.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply walk_suffix_nonnegative.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valid_table_initial_prefix_choice with (m := m_pre).
  exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CycleAnswer.
  split; [lia |].
  apply valid_factor_table_walk_spec_solver_order; try lia.
  - unfold Pre in PreH5. exact PreH5.
  - exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_5.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite unsigned_last_nbits_eq.
  - dump_pre_spatial.
    apply cycle_answer_to_spec; assumption.
  - unfold CycleAnswer in *; lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (UInt64Array.seg_to_seg_shape (&( "pr" )) 0 factor_count_2 pr_values).
  sep_apply_l_atomic
    (UInt64Array.seg_to_seg_shape (&( "pe" )) 0 factor_count_2 pe_values).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_1 : solver_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold WalkGlobalBounds, Pre in *; lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_2 : solver_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold WalkMachineBounds in *; lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_3 : solver_partial_solve_wit_7_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(unfold WalkBudget in *; lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_3.
Qed.
