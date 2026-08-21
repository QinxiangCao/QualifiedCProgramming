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
Require Import annoying_math_homework_goal.
Require Import annoying_math_homework_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib.
Local Open Scope sac.

Lemma proof_of_digits_sum_init_safety_wit_8_split_goal_1 : digits_sum_init_safety_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold PowerPrefix in PreH4.
  destruct PreH4 as [_ [_ Hforall]].
  assert (Hi: 0 <= (i-1-0) < i) by lia.
  specialize (Hforall (i-1-0) Hi).
  replace (Znth (i - 1 - 0) power_l 0) with (10 ^ (i - 1 - 0) mod digit_sum_modulus) by lia.
  unfold digit_sum_modulus in *.
  assert (Hmod: 10 ^ (i - 1 - 0) mod 1000000007 < 1000000007).
  {
    apply Z.mod_pos_bound.
    lia.
  }
  lia.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_8_split_goal_2 : digits_sum_init_safety_wit_8_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold PowerPrefix in PreH4.
  destruct PreH4 as [_ [_ Hforall]].
  assert (Hi: 0 <= (i-1-0) < i) by lia.
  specialize (Hforall (i-1-0) Hi).
  replace (Znth (i - 1 - 0) power_l 0) with (10 ^ (i - 1 - 0) mod digit_sum_modulus) by lia.
  unfold digit_sum_modulus in *.
  assert (Hmod: 0 <= 10 ^ (i - 1 - 0) mod 1000000007).
  {
    apply Z.mod_pos_bound.
    lia.
  }
  lia.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_8 : digits_sum_init_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_digits_sum_init_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_36_split_goal_1 : digits_sum_init_safety_wit_36_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitDPCellProgress in PreH8.
  destruct PreH8 as [_ [_ [_ [_ [_ [Hprev _]]]]]].
  specialize (Hprev (i - 1) k ltac:(lia) ltac:(lia)).
  rewrite Hprev.
  unfold PowerTable in PreH9.
  destruct PreH9 as [_ Hpower].
  rewrite Hpower by lia.
  unfold DigitDPValue.
  destruct (Z.eq_dec (i - 1) 1).
  - pose proof (Z.mod_pos_bound k digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hleft.
    pose proof (Z.mod_pos_bound (10 ^ (i - 2)) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hpower_bound.
    assert (Hprod : 0 <= (10 ^ (i - 2) mod digit_sum_modulus) * j)
      by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (Z.rem_bound_pos_pos
      ((10 ^ (i - 2) mod digit_sum_modulus) * j) 1000000007
      ltac:(lia) Hprod) as Hright.
    destruct Hleft as [Hleft0 Hleft1].
    destruct Hright as [Hright0 Hright1].
    unfold digit_sum_modulus in *.
    apply Z.le_trans with (1000000007 + 1000000007).
    + apply Z.add_le_mono.
      * exact (Z.lt_le_incl _ _ Hleft1).
      * exact (Z.lt_le_incl _ _ Hright1).
    + vm_compute; discriminate.
  - pose proof (Z.mod_pos_bound
      (k * 10 ^ (i - 1 - 1) + 45 * (i - 1 - 1) * 10 ^ (i - 1 - 2))
      digit_sum_modulus ltac:(unfold digit_sum_modulus; lia)) as Hleft.
    pose proof (Z.mod_pos_bound (10 ^ (i - 2)) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hpower_bound.
    assert (Hprod : 0 <= (10 ^ (i - 2) mod digit_sum_modulus) * j)
      by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (Z.rem_bound_pos_pos
      ((10 ^ (i - 2) mod digit_sum_modulus) * j) 1000000007
      ltac:(lia) Hprod) as Hright.
    destruct Hleft as [Hleft0 Hleft1].
    destruct Hright as [Hright0 Hright1].
    unfold digit_sum_modulus in *.
    apply Z.le_trans with (1000000007 + 1000000007).
    + apply Z.add_le_mono.
      * exact (Z.lt_le_incl _ _ Hleft1).
      * exact (Z.lt_le_incl _ _ Hright1).
    + vm_compute; discriminate.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_36_split_goal_2 : digits_sum_init_safety_wit_36_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitDPCellProgress in PreH8.
  destruct PreH8 as [_ [_ [_ [_ [_ [Hprev _]]]]]].
  specialize (Hprev (i - 1) k ltac:(lia) ltac:(lia)).
  rewrite Hprev.
  unfold PowerTable in PreH9.
  destruct PreH9 as [_ Hpower].
  rewrite Hpower by lia.
  unfold DigitDPValue.
  destruct (Z.eq_dec (i - 1) 1).
  - pose proof (Z.mod_pos_bound k digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hleft.
    pose proof (Z.mod_pos_bound (10 ^ (i - 2)) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hpower_bound.
    assert (Hprod : 0 <= (10 ^ (i - 2) mod digit_sum_modulus) * j)
      by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (Z.rem_bound_pos_pos
      ((10 ^ (i - 2) mod digit_sum_modulus) * j) 1000000007
      ltac:(lia) Hprod) as Hright.
    destruct Hleft as [Hleft0 Hleft1].
    destruct Hright as [Hright0 Hright1].
    unfold digit_sum_modulus in *.
    apply Z.le_trans with 0.
    + vm_compute; discriminate.
    + apply Z.add_nonneg_nonneg; assumption.
  - pose proof (Z.mod_pos_bound
      (k * 10 ^ (i - 1 - 1) + 45 * (i - 1 - 1) * 10 ^ (i - 1 - 2))
      digit_sum_modulus ltac:(unfold digit_sum_modulus; lia)) as Hleft.
    pose proof (Z.mod_pos_bound (10 ^ (i - 2)) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hpower_bound.
    assert (Hprod : 0 <= (10 ^ (i - 2) mod digit_sum_modulus) * j)
      by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (Z.rem_bound_pos_pos
      ((10 ^ (i - 2) mod digit_sum_modulus) * j) 1000000007
      ltac:(lia) Hprod) as Hright.
    destruct Hleft as [Hleft0 Hleft1].
    destruct Hright as [Hright0 Hright1].
    unfold digit_sum_modulus in *.
    apply Z.le_trans with 0.
    + vm_compute; discriminate.
    + apply Z.add_nonneg_nonneg; assumption.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_36 : digits_sum_init_safety_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_safety_wit_36_split_goal_1.
  - Goal_apply proof_of_digits_sum_init_safety_wit_36_split_goal_2.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_38_split_goal_1 : digits_sum_init_safety_wit_38_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold PowerTable in PreH9.
  destruct PreH9 as [_ Hforall].
  assert (Hi: 0 <= i-2 < 20) by lia.
  specialize (Hforall (i-2) Hi).
  replace (Znth (i - 2) power_l 0) with (10 ^ (i - 2) mod digit_sum_modulus) by lia.
  assert (Hmod: 10 ^ (i - 2) mod digit_sum_modulus < 1000000007).
  {
    unfold digit_sum_modulus.
    apply Z.mod_pos_bound.
    lia.
  }
  nia.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_38_split_goal_2 : digits_sum_init_safety_wit_38_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold PowerTable in PreH9.
  destruct PreH9 as [_ Hforall].
  assert (Hi: 0 <= i-2 < 20) by lia.
  specialize (Hforall (i-2) Hi).
  replace (Znth (i - 2) power_l 0) with (10 ^ (i - 2) mod digit_sum_modulus) by lia.
  assert (Hmod: 0 <= 10 ^ (i - 2) mod digit_sum_modulus).
  {
    unfold digit_sum_modulus.
    apply Z.mod_pos_bound.
    lia.
  }
  nia.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_38 : digits_sum_init_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_digits_sum_init_safety_wit_38_split_goal_2.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_47_split_goal_1 : digits_sum_init_safety_wit_47_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitDPCellProgress in PreH8.
  destruct PreH8 as
    [Hlen [Hplaces [Hleading [Hsuffix [Hbase [Hprev
      [Hdone [Hafter [Hfuture [partial [Hsum Hcell]]]]]]]]]]].
  unfold PowerTable in PreH9.
  destruct PreH9 as [_ Hpower].
  specialize (Hprev (i - 1) k ltac:(lia) ltac:(lia)).
  assert (Hprev_nonneg : 0 <= Znth ((i - 1) * 10 + k) dp_l 0).
  { rewrite Hprev.
    unfold DigitDPValue.
    destruct (Z.eq_dec (i - 1) 1).
    - apply (proj1 (Z.mod_pos_bound k digit_sum_modulus
        ltac:(unfold digit_sum_modulus; lia))).
    - apply (proj1 (Z.mod_pos_bound
        (k * 10 ^ (i - 1 - 1) + 45 * (i - 1 - 1) * 10 ^ (i - 1 - 2))
        digit_sum_modulus ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hpower_nonneg : 0 <= Znth (i - 2) power_l 0).
  { rewrite Hpower by lia.
    apply (proj1 (Z.mod_pos_bound (10 ^ (i - 2)) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hprod : 0 <= Znth (i - 2) power_l 0 * j)
    by (apply Z.mul_nonneg_nonneg; assumption).
  pose proof (Z.rem_bound_pos_pos
    (Znth (i - 2) power_l 0 * j) 1000000007 ltac:(lia) Hprod) as Hrem1.
  destruct Hrem1 as [Hrem10 Hrem11].
  assert (Hmoving_num : 0 <=
    Znth ((i - 1) * 10 + k) dp_l 0 +
      Z.rem (Znth (i - 2) power_l 0 * j) 1000000007)
    by (apply Z.add_nonneg_nonneg; assumption).
  pose proof (Z.rem_bound_pos_pos
    (Znth ((i - 1) * 10 + k) dp_l 0 +
      Z.rem (Znth (i - 2) power_l 0 * j) 1000000007)
    1000000007 ltac:(lia) Hmoving_num) as Hmoving.
  destruct Hmoving as [Hmoving0 Hmoving1].
  rewrite Hcell.
  pose proof (Z.mod_pos_bound
    (partial + k * 10 ^ (i - 2) * j) digit_sum_modulus
    ltac:(unfold digit_sum_modulus; lia)) as Hcurrent.
  destruct Hcurrent as [Hcurrent0 Hcurrent1].
  unfold digit_sum_modulus in *.
  apply Z.le_trans with (1000000007 + 1000000007).
  - apply Z.add_le_mono.
    + exact (Z.lt_le_incl _ _ Hcurrent1).
    + exact (Z.lt_le_incl _ _ Hmoving1).
  - vm_compute; discriminate.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_47_split_goal_2 : digits_sum_init_safety_wit_47_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitDPCellProgress in PreH8.
  destruct PreH8 as
    [Hlen [Hplaces [Hleading [Hsuffix [Hbase [Hprev
      [Hdone [Hafter [Hfuture [partial [Hsum Hcell]]]]]]]]]]].
  unfold PowerTable in PreH9.
  destruct PreH9 as [_ Hpower].
  specialize (Hprev (i - 1) k ltac:(lia) ltac:(lia)).
  assert (Hprev_nonneg : 0 <= Znth ((i - 1) * 10 + k) dp_l 0).
  { rewrite Hprev.
    unfold DigitDPValue.
    destruct (Z.eq_dec (i - 1) 1).
    - apply (proj1 (Z.mod_pos_bound k digit_sum_modulus
        ltac:(unfold digit_sum_modulus; lia))).
    - apply (proj1 (Z.mod_pos_bound
        (k * 10 ^ (i - 1 - 1) + 45 * (i - 1 - 1) * 10 ^ (i - 1 - 2))
        digit_sum_modulus ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hpower_nonneg : 0 <= Znth (i - 2) power_l 0).
  { rewrite Hpower by lia.
    apply (proj1 (Z.mod_pos_bound (10 ^ (i - 2)) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hprod : 0 <= Znth (i - 2) power_l 0 * j)
    by (apply Z.mul_nonneg_nonneg; assumption).
  pose proof (Z.rem_bound_pos_pos
    (Znth (i - 2) power_l 0 * j) 1000000007 ltac:(lia) Hprod) as Hrem1.
  destruct Hrem1 as [Hrem10 Hrem11].
  assert (Hmoving_num : 0 <=
    Znth ((i - 1) * 10 + k) dp_l 0 +
      Z.rem (Znth (i - 2) power_l 0 * j) 1000000007)
    by (apply Z.add_nonneg_nonneg; assumption).
  pose proof (Z.rem_bound_pos_pos
    (Znth ((i - 1) * 10 + k) dp_l 0 +
      Z.rem (Znth (i - 2) power_l 0 * j) 1000000007)
    1000000007 ltac:(lia) Hmoving_num) as Hmoving.
  destruct Hmoving as [Hmoving0 Hmoving1].
  rewrite Hcell.
  pose proof (Z.mod_pos_bound
    (partial + k * 10 ^ (i - 2) * j) digit_sum_modulus
    ltac:(unfold digit_sum_modulus; lia)) as Hcurrent.
  destruct Hcurrent as [Hcurrent0 Hcurrent1].
  unfold digit_sum_modulus in *.
  apply Z.le_trans with 0.
  - vm_compute; discriminate.
  - apply Z.add_nonneg_nonneg; assumption.
Qed.

Lemma proof_of_digits_sum_init_safety_wit_47 : digits_sum_init_safety_wit_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_safety_wit_47_split_goal_1.
  - Goal_apply proof_of_digits_sum_init_safety_wit_47_split_goal_2.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_1 : digits_sum_init_entail_wit_1.
Proof.
  aggressive_pre_process.
  Exists (1 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single power_pre 0 1).
    simpl Z.add.
    cancel (IntArray.seg power_pre 0 1 (1 :: nil)).
  - split_pures; dump_pre_spatial.
    + lia.
    + lia.
    + unfold PowerPrefix, digit_sum_modulus.
      simpl.
      repeat split; try lia.
      intros idx Hidx.
      replace idx with 0 by lia.
      reflexivity.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_2_split_goal_1 : digits_sum_init_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  pose proof PreH4 as Hprefix.
  replace
    (signed_last_nbits
      ((Znth (i - 1 - 0) power_l_2 0 * 10) % 1000000007) 32)
    with ((Znth (i - 1) power_l_2 0 * 10) mod 1000000007).
  - (*intros power_l i Hi_lt Hi_lo Hi_hi Hprefix.*)
    unfold PowerPrefix in *.
    destruct Hprefix as [Hlen [Hbounds Hpower]].
    repeat split.
    + rewrite Zlength_app, Hlen, Zlength_cons, Zlength_nil.
      lia.
    + lia.
    + lia.
    + intros idx Hidx.
      destruct (Z_lt_ge_dec idx i) as [Hlt | Hge].
      * rewrite Znth_app_left__digits_power_and_zero_init by lia.
        apply Hpower; lia.
      * assert (idx = i) by lia; subst idx.
        replace i with (Zlength power_l_2) at 1 by lia.
        rewrite Znth_app_last__digits_power_and_zero_init.
        rewrite Hpower by lia.
        unfold digit_sum_modulus.
        replace i with (Z.succ (i - 1)) at 2 by lia.
        rewrite Z.pow_succ_r by lia.
        rewrite Z.mul_mod_idemp_l by lia.
        rewrite Z.mul_comm.
        reflexivity.
  - unfold PowerPrefix in Hprefix.
    destruct Hprefix as [Hlen [Hbounds Hpower]].
    rewrite Hpower by lia.
    replace (i - 1 - 0) with (i - 1) by lia.
    rewrite Hpower by lia.
    unfold digit_sum_modulus in *.
    pose proof (Z.mod_pos_bound (10 ^ (i - 1)) 1000000007 ltac:(lia)) as Hinner.
    assert (Hprod : 0 <= 10 ^ (i - 1) mod 1000000007 * 10) by nia.
    rewrite (Z.rem_mod_nonneg
        (10 ^ (i - 1) mod 1000000007 * 10) 1000000007 Hprod ltac:(lia)).
    pose proof (Z.mod_pos_bound
        (10 ^ (i - 1) mod 1000000007 * 10) 1000000007 ltac:(lia)) as Hmod.
    symmetry; apply signed_last_nbits_eq; lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_2 : digits_sum_init_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_3 : digits_sum_init_entail_wit_3.
Proof.
  aggressive_pre_process.
  Exists (@nil Z).
  split_pure_spatial.
  - sep_apply (IntArray.undef_full_to_undef_seg dp_pre 200).
    simpl Z.mul.
    rewrite IntArray.seg_empty.
    cancel (IntArray.undef_seg dp_pre 0 200).
    split_pure_spatial.
    + easy.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + lia.
    + unfold ZeroSegment.
      simpl.
      repeat split; try lia.
    + unfold PowerPrefix in PreH4.
      unfold PowerTable.
      destruct PreH4 as [Hlen [_ Hpower]].
      subst i.
      split; [lia |].
      intros idx Hidx.
      apply Hpower.
      lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_4 : digits_sum_init_entail_wit_4.
Proof.
  aggressive_pre_process.
  Exists dp_l_2.
  replace (i * 10 + 0) with (i * 10) by lia.
  split_pure_spatial.
  - cancel (IntArray.seg dp_pre 0 (i * 10) dp_l_2).
  - split_pures; dump_pre_spatial; first [lia | assumption].
Qed.

Lemma proof_of_digits_sum_init_entail_wit_5 : digits_sum_init_entail_wit_5.
Proof.
  aggressive_pre_process.
  Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - replace (i * 10 + (j + 1)) with (i * 10 + j + 1) by lia.
    cancel (IntArray.seg dp_pre 0 (i * 10 + j + 1) (dp_l_2 ++ 0 :: nil)).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    replace (i * 10 + (j + 1)) with ((i * 10 + j) + 1) by lia.
    apply ZeroSegment_app_zero__digits_power_and_zero_init; try assumption.
    unfold ZeroSegment in PreH6.
    lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_6 : digits_sum_init_entail_wit_6.
Proof.
  aggressive_pre_process.
  Exists dp_l_2.
  assert (j = 10) by lia; subst j.
  replace ((i + 1) * 10) with (i * 10 + 10) by lia.
  split_pure_spatial.
  - cancel (IntArray.seg dp_pre 0 (i * 10 + 10) dp_l_2).
  - split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_7_split_goal_1 : digits_sum_init_entail_wit_7_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ZeroSegment in PreH4.
  unfold DigitDPBaseProgress.
  destruct PreH4 as [Hlen [Hbounds Hzero]].
  repeat split; try lia.
  intros k Hk _.
  apply Hzero; lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_7 : digits_sum_init_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_8_split_goal_1 : digits_sum_init_entail_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPBaseProgress in *.
  repeat split; try lia.
  - replace 200 with (Zlength dp_l_2) by lia.
    apply (Zlength_replace_Znth dp_l_2 (10+j) j).
  - intros j0 Hj0.
    destruct PreH4 as [Hlength [_ [Hforall1 _]]].
    destruct (Z.eq_dec j j0) as [Heq | Hneq].
    + subst j0.
      apply (Znth_replace_Znth_Same 0 dp_l_2 (10+j) j); lia.
    + assert (Hj0': 0 <= j0 < j) by lia.
      assert (Hreplace: Znth (10 + j0) (replace_Znth (10 + j) j dp_l_2) 0 = Znth (10 + j0) dp_l_2 0).
      {
        apply (Znth_replace_Znth_Diff 0 dp_l_2 (10+j) (10+j0) j); lia.
      }
      replace (Znth (10 + j0) (replace_Znth (10 + j) j dp_l_2) 0) with (Znth (10 + j0) dp_l_2 0) by lia.
      apply Hforall1; lia.
  - intros k Hk1 Hk2.
    assert (Hreplace : Znth k (replace_Znth (10 + j) j dp_l_2) 0 = Znth k dp_l_2 0).
    {
      apply (Znth_replace_Znth_Diff 0 dp_l_2 (10+j) k j); lia.
    }
    replace (Znth k (replace_Znth (10 + j) j dp_l_2) 0) with (Znth k dp_l_2 0) by lia.
    destruct PreH4 as [_ [_ [_ Hforall2]]].
    apply Hforall2; lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_8 : digits_sum_init_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_8_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_9_split_goal_1 : digits_sum_init_entail_wit_9_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPOuterProgress.
  unfold DigitDPBaseProgress in PreH4.
  destruct PreH4 as [Hlength [Hj [Hdpold Hdpnew]]].
  assert (j = 10) by lia. subst j.
  repeat split; try tauto; try lia.
  - intros d Hd.
    apply Hdpnew; lia.
  - intros places leading Hplaces Hleading.
    unfold DigitDPValue.
    destruct (Z.eq_dec places 1) as [H_places_eq1 | H_places_neq1].
    + subst places.
      specialize (Hdpold leading Hleading).
      replace (Znth (1 * 10 + leading) dp_l_2 0) with leading.
      unfold digit_sum_modulus.
      pose proof Z.mod_small as Hmod.
      assert (Hleading': 0 <= leading < 1000000007) by lia.
      specialize (Hmod leading 1000000007 Hleading').
      lia.
    + exfalso; lia.
  - intros places leading Hplaces Hleading.
    set (k := places * 10 + leading).
    assert (Hk : 20 <= k < 200) by lia.
    apply Hdpnew; lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_9 : digits_sum_init_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_10_split_goal_1 : digits_sum_init_entail_wit_10_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPRowProgress.
  unfold DigitDPOuterProgress in PreH4.
  destruct PreH4 as [Hlength [_ [Hforall1 [Hforall2 Hforall3]]]].
  repeat split; try assumption; try tauto; try lia.
  - intros d Hd.
    specialize (Hforall3 i d ltac:(lia) Hd).
    exact Hforall3.
  - intros p d Hp Hd.
    assert (Hp': i <= p < 20) by lia.
    specialize (Hforall3 p d Hp' Hd).
    exact Hforall3.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_10 : digits_sum_init_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_10_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_11_split_goal_1 : digits_sum_init_entail_wit_11_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPCellProgress.
  unfold DigitDPRowProgress in PreH6.
  repeat split; try assumption; try tauto; try lia.
  - intros d Hd.
    destruct PreH6 as [_ [_ [_ [_ [_ [_ [Hforall _]]]]]]].
    apply Hforall.
    lia.
  - exists 0. split.
    + apply InnerCandidateDigitSum_zero.
    + replace ((0 + 0 * 10 ^ (i - 2) * j) mod digit_sum_modulus) with 0.
      * destruct PreH6 as [_ [_ [_ [_ [_ [_ [Hforall _]]]]]]].
        apply Hforall.
        lia.
      * replace (0 + 0 * 10 ^ (i - 2) * j) with 0 by lia.
        pose proof Zmod_0_l as Hmod.
        specialize (Hmod digit_sum_modulus).
        lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_11 : digits_sum_init_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_11_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_12_split_goal_1 : digits_sum_init_entail_wit_12_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPCellProgress in PreH8.
  destruct PreH8 as
    [Hlen [Hplaces [Hleading [Hnext
      [Hbase [Hprevious [Hdone [Hzero [Hlater
        [partial [Hinner Hcell]]]]]]]]]]].
  unfold PowerTable in PreH9.
  destruct PreH9 as [Hpower_len Hpower].
  specialize (Hpower (i - 2) ltac:(lia)).
  assert (Hpower_nonnegative : 0 <= Znth (i - 2) power_l_2 0).
  { rewrite Hpower.
    exact (proj1 (Z.mod_pos_bound (10 ^ (i - 2))
      digit_sum_modulus ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hprevious_nonnegative :
    0 <= Znth ((i - 1) * 10 + k) dp_l_2 0).
  { rewrite Hprevious by lia.
    unfold DigitDPValue.
    destruct (Z.eq_dec (i - 1) 1);
      exact (proj1 (Z.mod_pos_bound _ digit_sum_modulus
        ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hcell_nonnegative : 0 <= Znth (i * 10 + j) dp_l_2 0).
  { rewrite Hcell.
    exact (proj1 (Z.mod_pos_bound
      (partial + k * 10 ^ (i - 2) * j) digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia))). }
  rewrite (Z.rem_mod_nonneg
    (Znth (i - 2) power_l_2 0 * j) 1000000007) by nia.
  pose proof (Z.mod_pos_bound
    (Znth (i - 2) power_l_2 0 * j) 1000000007 ltac:(lia)) as Hinner_mod.
  rewrite (Z.rem_mod_nonneg
    (Znth ((i - 1) * 10 + k) dp_l_2 0 +
     (Znth (i - 2) power_l_2 0 * j) mod 1000000007)
    1000000007) by nia.
  pose proof (Z.mod_pos_bound
    (Znth ((i - 1) * 10 + k) dp_l_2 0 +
     (Znth (i - 2) power_l_2 0 * j) mod 1000000007)
    1000000007 ltac:(lia)) as Hmiddle_mod.
  rewrite (Z.rem_mod_nonneg
    (Znth (i * 10 + j) dp_l_2 0 +
     (Znth ((i - 1) * 10 + k) dp_l_2 0 +
      (Znth (i - 2) power_l_2 0 * j) mod 1000000007) mod
      1000000007)
    1000000007) by nia.
  unfold signed_last_nbits.
  set (raw :=
    ((Znth (i * 10 + j) dp_l_2 0 +
      (Znth ((i - 1) * 10 + k) dp_l_2 0 +
       (Znth (i - 2) power_l_2 0 * j) mod 1000000007) mod
       1000000007) mod 1000000007)).
  set (cell :=
    (let v := raw mod (2 ^ 32) in
     if Coqlib.zlt v (2 ^ (32 - 1)) then v else v - 2 ^ 32)).
  unfold DigitDPCellProgress.
  rewrite Zlength_replace_Znth__digits_dp_cell.
  repeat split; try lia; try assumption.
  - intros d Hd.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hbase; exact Hd.
  - intros p d Hp Hd.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hprevious; assumption.
  - intros d Hd.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hdone; exact Hd.
  - intros d Hd.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hzero; exact Hd.
  - intros p d Hp Hd.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hlater; assumption.
  - exists ((partial + Znth ((i - 1) * 10 + k) dp_l_2 0) mod
      digit_sum_modulus).
    split.
    + rewrite <- (Znth_replace_Znth_Diff 0 dp_l_2
        (i * 10 + j) ((i - 1) * 10 + k) cell)
        by (try rewrite Hlen; lia).
      apply InnerCandidateDigitSum_step.
      * lia.
      * eapply InnerCandidateDigitSum_replace_other__digits_dp_cell.
        -- try rewrite Hlen; lia.
        -- intros next Hnext'. split; try rewrite Hlen; lia.
        -- exact Hinner.
    + rewrite Znth_replace_Znth_Same by (try rewrite Hlen; lia).
      unfold cell.
      assert (Hraw_bounds : 0 <= raw < 1000000007).
      { unfold raw. apply Z.mod_pos_bound. lia. }
      cbn zeta.
      rewrite Z.mod_small by
        (change (2 ^ 32) with 4294967296; lia).
      destruct (Coqlib.zlt raw (2 ^ (32 - 1))) as [Hsmall | Hlarge].
      2: { change (2 ^ (32 - 1)) with 2147483648 in Hlarge; lia. }
      unfold raw.
      rewrite Hcell, Hpower.
      unfold digit_sum_modulus.
      apply (digit_dp_cell_mod_update__digits_dp_cell
        partial (Znth ((i - 1) * 10 + k) dp_l_2 0)
        (10 ^ (i - 2)) k j 1000000007).
      lia.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_12 : digits_sum_init_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_12_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_13_split_goal_1 : digits_sum_init_entail_wit_13_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPCellProgress in PreH8.
  destruct PreH8 as
    [Hlen [Hplaces [Hleading [Hnext
      [Hbase [Hprevious [Hdone [Hzero [Hlater
        [partial [Hinner Hcell]]]]]]]]]]].
  assert (k = 10) by lia.
  subst k.
  unfold DigitDPRowProgress.
  split; [exact Hlen |].
  split; [exact Hplaces |].
  split; [lia |].
  split; [exact Hbase |].
  split; [exact Hprevious |].
  split.
  - intros d Hd.
    destruct (Z_lt_ge_dec d j) as [Hdlt | Hdge].
    + apply Hdone.
      lia.
    + assert (d = j) by lia.
      subst d.
      rewrite Hcell.
      pose proof (InnerCandidateDigitSum_ten__digits_dp_row
        dp_l_2 (i - 1) partial ltac:(lia)
        (fun suffix Hsuffix =>
          Hprevious (i - 1) suffix ltac:(lia) Hsuffix)
        Hinner) as Hpartial.
      rewrite Hpartial.
      unfold DigitDPValue.
      destruct (Z.eq_dec i 1) as [Heq | Hneq]; [lia |].
      rewrite Z.add_mod_idemp_l by
        (unfold digit_sum_modulus; lia).
      assert (Hpow :
        10 ^ (i - 1) = 10 * 10 ^ (i - 2)).
      {
        replace (i - 1) with (Z.succ (i - 2)) by lia.
        rewrite Z.pow_succ_r by lia.
        ring.
      }
      rewrite Hpow.
      f_equal.
      replace (i - 1 - 1) with (i - 2) by lia.
      ring.
  - split.
    + intros d Hd.
      apply Hzero.
      lia.
    + intros p d Hp Hd.
      apply Hlater; assumption.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_13 : digits_sum_init_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_14_split_goal_1 : digits_sum_init_entail_wit_14_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPOuterProgress.
  unfold DigitDPRowProgress in PreH6.
  assert (j = 10) by lia; subst j.
  repeat split; try assumption; try tauto; try lia.
  - intros places leading Hplaces Hleading.
    destruct (Z.eq_dec places i) as [Hplaces_eq | Hplaces_neq].
    + subst places.
      destruct PreH6 as [_ [_ [_ [_ [_ [Hforall _]]]]]].
      specialize (Hforall leading Hleading).
      exact Hforall.
    + assert (Hplaces': 1 <= places < i) by lia.
      destruct PreH6 as [_ [_ [_ [_ [Hforall _]]]]].
      specialize (Hforall places leading Hplaces' Hleading).
      exact Hforall.
  - intros places leading Hplaces Hleading.
    assert (Hplaces': i < places < 20) by lia.
    destruct PreH6 as [_ [_ [_ [_ [_ [_ [_ Hforall]]]]]]].
    specialize (Hforall places leading Hplaces' Hleading).
    exact Hforall.
Qed.

Lemma proof_of_digits_sum_init_entail_wit_14 : digits_sum_init_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_digits_sum_init_return_wit_1_split_goal_1 : digits_sum_init_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitDPTable.
  unfold DigitDPOuterProgress in PreH4.
  repeat split; try assumption; try tauto; try lia.
  assert (i = 20) by lia; subst i.
  intros places leading Hplaces Hleading.
  destruct PreH4 as [_ [_ [_ [Hforall _]]]].
  apply Hforall; lia.
Qed.

Lemma proof_of_digits_sum_init_return_wit_1 : digits_sum_init_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_digits_sum_init_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_17_split_goal_1 : prefix_digits_sum_safety_wit_17_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitPositionPower in PreH11.
  destruct PreH11 as [[Hi Hile] Hpower].
  subst power_ll.
  assert (Hpow : 10 ^ (i - 1) <= 10 ^ 17).
  { apply Z.pow_le_mono_r; lia. }
  change (10 ^ (i - 1) <= 100000000000000000) in Hpow.
  nia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_17_split_goal_2 : prefix_digits_sum_safety_wit_17_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitPositionPower in PreH11.
  destruct PreH11 as [[Hi Hile] Hpower].
  subst power_ll.
  assert (Hpow : 0 <= 10 ^ (i - 1)).
  { apply Z.pow_nonneg; lia. }
  nia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_17 : prefix_digits_sum_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_23_split_goal_1 : prefix_digits_sum_safety_wit_23_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitDPTable in PreH19.
  destruct PreH19 as [_ [_ Hcell]].
  assert (Hi: 1 <= i < 20) by lia.
  assert (Hj: 0 <= j < 10) by lia.
  specialize (Hcell i j Hi Hj).
  rewrite Hcell.
  unfold DigitDPValue.
  destruct (Z.eq_dec i 1) as [Heq | Hneq].
  - subst i.
    pose proof (Z.mod_pos_bound j digit_sum_modulus ltac:(unfold digit_sum_modulus; lia)) as Hmod.
    unfold digit_sum_modulus in *.
    lia.
  - pose proof (Z.mod_pos_bound
      (j * 10 ^ (i - 1) + 45 * (i - 1) * 10 ^ (i - 2))
      digit_sum_modulus ltac:(unfold digit_sum_modulus; lia)) as Hmod.
    unfold digit_sum_modulus in *.
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_23_split_goal_2 : prefix_digits_sum_safety_wit_23_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold DigitDPTable in PreH19.
  destruct PreH19 as [_ [_ Hcell]].
  assert (Hi: 1 <= i < 20) by lia.
  assert (Hj: 0 <= j < 10) by lia.
  specialize (Hcell i j Hi Hj).
  rewrite Hcell.
  unfold DigitDPValue.
  destruct (Z.eq_dec i 1) as [Heq | Hneq].
  - subst i.
    pose proof (Z.mod_pos_bound j digit_sum_modulus ltac:(unfold digit_sum_modulus; lia)) as Hmod.
    unfold digit_sum_modulus in *.
    lia.
  - pose proof (Z.mod_pos_bound
      (j * 10 ^ (i - 1) + 45 * (i - 1) * 10 ^ (i - 2))
      digit_sum_modulus ltac:(unfold digit_sum_modulus; lia)) as Hmod.
    unfold digit_sum_modulus in *.
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_23 : prefix_digits_sum_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_30_split_goal_1 : prefix_digits_sum_safety_wit_30_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hlo Hhi] Hpow]].
  - lia.
  - subst power_ll. right.
    assert (Hpos : 0 < 10 ^ (i - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_30_split_goal_2 : prefix_digits_sum_safety_wit_30_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hlo Hhi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_30 : prefix_digits_sum_safety_wit_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_30_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_30_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_33_split_goal_1 : prefix_digits_sum_safety_wit_33_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold ExtractedDigitCount in PreH15.
  destruct PreH15 as [[Hcountlo Hcounthi] [Hxlo Hxhi]].
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hilo Hihi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    assert (Hbound : 10 ^ (i - 1) <= 10 ^ 18).
    { apply Z.pow_le_mono_r; lia. }
    change (10 ^ (i - 1) <= 1000000000000000000) in Hbound.
    assert (Hxpos : 0 < x_pre).
    { assert (0 < 10 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    pose proof (Z.rem_bound_pos_pos x_pre (10 ^ (i - 1)) Hpos ltac:(lia)) as Hrem.
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_33_split_goal_2 : prefix_digits_sum_safety_wit_33_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold ExtractedDigitCount in PreH15.
  destruct PreH15 as [[Hcountlo Hcounthi] [Hxlo Hxhi]].
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hilo Hihi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    assert (Hxpos : 0 < x_pre).
    { assert (0 < 10 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    pose proof (Z.rem_bound_pos_pos x_pre (10 ^ (i - 1)) Hpos ltac:(lia)) as Hrem.
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_33 : prefix_digits_sum_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_34_split_goal_1 : prefix_digits_sum_safety_wit_34_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hlo Hhi] Hpow]].
  - lia.
  - subst power_ll.
    right.
    assert (Hpos : 0 < 10 ^ (i - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_34_split_goal_2 : prefix_digits_sum_safety_wit_34_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hlo Hhi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_34 : prefix_digits_sum_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_34_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_38_split_goal_1 : prefix_digits_sum_safety_wit_38_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold ExtractedDigitCount in PreH15.
  destruct PreH15 as [[Hcountlo Hcounthi] [Hxlo Hxhi]].
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hilo Hihi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hxpos : 0 < x_pre).
    { assert (0 < 10 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    pose proof (Z.rem_bound_pos_pos x_pre (10 ^ (i - 1)) Hpos ltac:(lia)) as Hinner.
    pose proof (Z.rem_bound_pos_pos (Z.rem x_pre (10 ^ (i - 1)) + 1)
      1000000007 ltac:(lia) ltac:(lia)) as Hlow.
    assert (Hquot : 0 <= Z.quot x_pre (10 ^ (i - 1))) by (apply Z.quot_pos; lia).
    pose proof (Z.rem_bound_pos_pos (Z.quot x_pre (10 ^ (i - 1))) 10
      ltac:(lia) ltac:(lia)) as Hdigit.
    nia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_38_split_goal_2 : prefix_digits_sum_safety_wit_38_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold ExtractedDigitCount in PreH15.
  destruct PreH15 as [[Hcountlo Hcounthi] [Hxlo Hxhi]].
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hilo Hihi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hxpos : 0 < x_pre).
    { assert (0 < 10 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    pose proof (Z.rem_bound_pos_pos x_pre (10 ^ (i - 1)) Hpos ltac:(lia)) as Hinner.
    pose proof (Z.rem_bound_pos_pos (Z.rem x_pre (10 ^ (i - 1)) + 1)
      1000000007 ltac:(lia) ltac:(lia)) as Hlow.
    assert (Hquot : 0 <= Z.quot x_pre (10 ^ (i - 1))) by (apply Z.quot_pos; lia).
    pose proof (Z.rem_bound_pos_pos (Z.quot x_pre (10 ^ (i - 1))) 10
      ltac:(lia) ltac:(lia)) as Hdigit.
    nia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_38 : prefix_digits_sum_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_38_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_41_split_goal_1 : prefix_digits_sum_safety_wit_41_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold ExtractedDigitCount in PreH15.
  destruct PreH15 as [[Hcountlo Hcounthi] [Hxlo Hxhi]].
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hilo Hihi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hxpos : 0 < x_pre).
    { assert (0 < 10 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    pose proof (Z.rem_bound_pos_pos x_pre (10 ^ (i - 1)) Hpos ltac:(lia)) as Hinner.
    pose proof (Z.rem_bound_pos_pos (Z.rem x_pre (10 ^ (i - 1)) + 1)
      1000000007 ltac:(lia) ltac:(lia)) as Hlow.
    assert (Hquot : 0 <= Z.quot x_pre (10 ^ (i - 1))) by (apply Z.quot_pos; lia).
    pose proof (Z.rem_bound_pos_pos (Z.quot x_pre (10 ^ (i - 1))) 10
      ltac:(lia) ltac:(lia)) as Hdigit.
    pose proof (Z.rem_bound_pos_pos
      (Z.rem (Z.rem x_pre (10 ^ (i - 1)) + 1) 1000000007 *
       Z.rem (Z.quot x_pre (10 ^ (i - 1))) 10)
      1000000007 ltac:(nia) ltac:(lia)) as Hmoving.
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_41_split_goal_2 : prefix_digits_sum_safety_wit_41_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold ExtractedDigitCount in PreH15.
  destruct PreH15 as [[Hcountlo Hcounthi] [Hxlo Hxhi]].
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hz Hzero] | [[Hilo Hihi] Hpow]].
  - lia.
  - subst power_ll.
    assert (Hpos : 0 < 10 ^ (i - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hxpos : 0 < x_pre).
    { assert (0 < 10 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    pose proof (Z.rem_bound_pos_pos x_pre (10 ^ (i - 1)) Hpos ltac:(lia)) as Hinner.
    pose proof (Z.rem_bound_pos_pos (Z.rem x_pre (10 ^ (i - 1)) + 1)
      1000000007 ltac:(lia) ltac:(lia)) as Hlow.
    assert (Hquot : 0 <= Z.quot x_pre (10 ^ (i - 1))) by (apply Z.quot_pos; lia).
    pose proof (Z.rem_bound_pos_pos (Z.quot x_pre (10 ^ (i - 1))) 10
      ltac:(lia) ltac:(lia)) as Hdigit.
    pose proof (Z.rem_bound_pos_pos
      (Z.rem (Z.rem x_pre (10 ^ (i - 1)) + 1) 1000000007 *
       Z.rem (Z.quot x_pre (10 ^ (i - 1))) 10)
      1000000007 ltac:(nia) ltac:(lia)) as Hmoving.
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_safety_wit_41 : prefix_digits_sum_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_safety_wit_41_split_goal_2.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_1_split_goal_1 : prefix_digits_sum_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ZeroSegment.
  repeat split.
  - reflexivity.
  - lia.
  - intros k Hk. lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_1 : prefix_digits_sum_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_2_split_goal_1 : prefix_digits_sum_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ZeroSegment in PreH9 |- *.
  destruct PreH9 as [Hlen [Hbounds Hzero]].
  split.
  - rewrite Zlength_app, Hlen. simpl. reflexivity.
  - split.
    + lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i).
      * rewrite app_Znth1 by lia.
        apply Hzero. lia.
      * assert (k = i) by lia. subst k.
        rewrite app_Znth2 by lia.
        replace (i - Zlength digits_l_2) with 0 by lia.
        reflexivity.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_2 : prefix_digits_sum_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_3_split_goal_1 : prefix_digits_sum_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ZeroSegment in PreH9.
  unfold ExtractedDigitBuffer.
  destruct PreH9 as [Hlen [Hbounds Hzero]].
  assert (Hi : i = 20) by lia.
  assert (Hlen20 : Zlength digits_l_2 = 20) by lia.
  subst m.
  split; [exact Hlen20 |].
  split.
  - split; lia.
  - split.
    + change (x_pre = x_pre / 1).
      rewrite Z.div_1_r. reflexivity.
    + split.
      * intros k Hk. lia.
      * intros k Hk. apply Hzero. lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_3 : prefix_digits_sum_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_4_split_goal_1 : prefix_digits_sum_entail_wit_4_split_goal_1.
Proof.
  aggressive_pre_process.
  intros.
  unfold ExtractedDigitBuffer in PreH11 |- *.
  destruct PreH11 as [Hlen [Hcount [Hremaining [Hdigits Hzero]]]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + split; lia.
    + split.
      * rewrite Hremaining.
        rewrite Z.quot_div_nonneg by (try lia; apply Z.div_pos; lia).
        rewrite Z.div_div; [| apply Z.pow_nonzero; lia | lia].
        f_equal.
        replace (m + 1) with (Z.succ m) by lia.
        rewrite Z.pow_succ_r by lia.
        ring.
      * split.
        -- intros k Hk.
           destruct (Z.eq_dec k (m + 1)).
           ++ subst k.
              rewrite Znth_replace_Znth_Same by lia.
              replace (m + 1 - 1) with m by lia.
              rewrite <- Hremaining.
              rewrite Z.rem_mod_nonneg by lia.
              destruct (Z.mod_pos_bound tmpx 10 ltac:(lia)) as [Hmodlo Hmodhi].
              pose proof signed_last_nbits_small as Hlastbits.
              assert (H32: 32 > 0) by lia.
              assert (Htmpx: 0 <= (tmpx mod 10) < (2 ^ 31)) by lia.
              specialize (Hlastbits (tmpx mod 10) 32 H32 Htmpx).
              exact Hlastbits.
           ++ rewrite Znth_replace_Znth_Diff by lia.
              apply Hdigits. lia.
        -- intros k Hk.
           rewrite Znth_replace_Znth_Diff by lia.
           apply Hzero. lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_4_split_goal_2 : prefix_digits_sum_entail_wit_4_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof H as Hzero.
  unfold ExtractedDigitBuffer in PreH11.
  destruct PreH11 as [_ [_ [Hremaining _]]].
  unfold ExtractedDigitCount.
  assert (Hp : 0 < 10 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (Htmp_one : 1 <= tmpx) by lia.
  rewrite Z.quot_div_nonneg in Hzero by lia.
  pose proof (Z.div_mod tmpx 10 ltac:(lia)) as Htmp_decomp.
  destruct (Z.mod_pos_bound tmpx 10 ltac:(lia)) as [Htmp_mod0 Htmp_mod10].
  assert (Htmp_ten : tmpx < 10) by nia.
  pose proof (Z.div_mod x_pre (10 ^ m) ltac:(lia)) as Hx_decomp.
  destruct (Z.mod_pos_bound x_pre (10 ^ m) Hp) as [Hx_mod0 Hx_modp].
  split; [lia|].
  split.
  - replace (m + 1 - 1) with m by lia. nia.
  - replace (m + 1) with (Z.succ m) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_4_split_goal_3 : prefix_digits_sum_entail_wit_4_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold ExtractedDigitBuffer in PreH11.
  destruct PreH11 as [_ [_ [Hremaining _]]].
  subst tmpx.
  assert (Hm : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/
    m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/
    m = 11 \/ m = 12 \/ m = 13 \/ m = 14 \/ m = 15 \/
    m = 16 \/ m = 17 \/ m = 18) by lia.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  end; subst m; simpl in *; try nia.
  exfalso.
  apply H.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_small.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_4_split_goal_4 : prefix_digits_sum_entail_wit_4_split_goal_4.
Proof.
  aggressive_pre_process.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod tmpx 10 ltac:(lia)) as Hdecomp.
  destruct (Z.mod_pos_bound tmpx 10 ltac:(lia)) as [Hmodlo Hmodhi].
  nia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_4 : prefix_digits_sum_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_5_split_goal_1 : prefix_digits_sum_entail_wit_5_split_goal_1.
Proof.
  aggressive_pre_process.
  subst ans.
  apply AccumulatedDigitSumCorrect_initial.
  - exact PreH1.
  - apply PreH10.
    exact PreH13.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_5_split_goal_2 : prefix_digits_sum_entail_wit_5_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold OuterDigitPositionProgress.
  subst tmpx.
  subst ans.
  constructor.
  - exact PreH11.
  - apply PreH10.
    reflexivity.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_5_split_goal_3 : prefix_digits_sum_entail_wit_5_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold DigitPositionPower.
  subst power_ll.
  simpl.
  lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_5 : prefix_digits_sum_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_6_split_goal_1 : prefix_digits_sum_entail_wit_6_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitPositionPower in PreH11 |- *.
  destruct PreH11 as [Hrange Hpower].
  split; [lia|].
  rewrite Hpower.
  replace (10 ^ (i - 1) * 10) with (10 * 10 ^ (i - 1)) by ring.
  rewrite <- Z.pow_succ_r by lia.
  f_equal. lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_6 : prefix_digits_sum_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_7_split_goal_1 : prefix_digits_sum_entail_wit_7_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold DigitPositionPower in PreH11.
  unfold OuterDigitPositionPower.
  right.
  destruct PreH11 as [Hrange Hpower].
  assert (i = m) by lia.
  subst i.
  exact (conj Hrange Hpower).
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_7 : prefix_digits_sum_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_8 : prefix_digits_sum_entail_wit_8.
Proof.
  aggressive_pre_process.
  pose proof PreH10 as Hbuffer.
  unfold ExtractedDigitBuffer in Hbuffer.
  destruct Hbuffer as [_ [_ [_ [Hdigits _]]]].
  specialize (Hdigits i ltac:(lia)).
  pose proof (Z.mod_pos_bound (x_pre / 10 ^ (i - 1)) 10 ltac:(lia)) as Hdigit_bounds.
  rewrite <- Hdigits in Hdigit_bounds.
  Exists ans.
  split_pure_spatial.
  - easy.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold InnerCandidateDigitProgress.
    split; [lia|].
    split; [lia|].
    split; [exact PreH12|].
    exists 0.
    split.
    + constructor.
    + unfold digit_sum_modulus.
      rewrite Z.add_0_r.
      rewrite Z.mod_small by lia.
      reflexivity.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_9 : prefix_digits_sum_entail_wit_9.
Proof.
  aggressive_pre_process.
  pose proof PreH19 as Htable.
  unfold DigitDPTable in Htable.
  destruct Htable as [_ [_ Htable]].
  specialize (Htable i j ltac:(lia) ltac:(lia)).
  pose proof
    (DigitDPValue_nonnegative__prefix_inner_outer_scan i j) as Hdp_nonneg.
  rewrite <- Htable in Hdp_nonneg.
  pose proof (Z.mod_pos_bound
    (ans + Znth (i * 10 + j) dp_l 0) 1000000007 ltac:(lia)) as Hmod_bounds.
  Exists answer_before_2.
  split_pure_spatial.
  - easy.
  - split_pures; dump_pre_spatial;
      try (rewrite Z.rem_mod_nonneg by lia); try lia; try assumption.
    unfold InnerCandidateDigitProgress in *.
    destruct PreH16 as [Hplaces [Hnext [Houter [choice_sum [Hchoice Hans]]]]].
    split; [lia|].
    split; [lia|].
    split; [exact Houter|].
    exists ((choice_sum + Znth (i * 10 + j) dp_l 0) mod digit_sum_modulus).
    split.
    + apply InnerCandidateDigitSum_step; try lia.
      exact Hchoice.
    + subst ans.
      unfold digit_sum_modulus.
      rewrite Z.add_mod_idemp_l by lia.
      rewrite Z.add_mod_idemp_r by lia.
      f_equal.
      ring.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_10_split_goal_1 : prefix_digits_sum_entail_wit_10_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply outer_power_predecessor__prefix_inner_outer_scan.
  - exact PreH5.
  - exact PreH18.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_10_split_goal_2 : prefix_digits_sum_entail_wit_10_split_goal_2.
Proof.
  aggressive_pre_process.
  assert (Hjeq : j = Znth i digits_l_2 0) by lia.
  unfold InnerCandidateDigitProgress in PreH16.
  destruct PreH16 as
    [Hplaces [Hnext [Houter [choice_sum [Hchoice HansEq]]]]].
  assert (Hsemantic :
    AccumulatedDigitSumCorrect x_pre (i - 1)
      ((answer_before + choice_sum +
        (((x_pre mod 10 ^ (i - 1)) + 1) mod digit_sum_modulus) *
          Znth i digits_l_2 0) mod digit_sum_modulus)).
  {
    eapply AccumulatedDigitSumCorrect_step
      with (count := m) (dp := dp_l) (digits := digits_l_2)
        (choice_sum := choice_sum).
    - exact PreH2.
    - lia.
    - exact PreH7.
    - exact PreH14.
    - exact PreH19.
    - rewrite <- Hjeq.
      exact Hchoice.
    - exact PreH17.
  }
  unfold OuterDigitPositionPower in PreH18.
  destruct PreH18 as [[Hposition_zero _] | [[_ _] Hpower]]; [lia|].
  pose proof PreH14 as Hbuffer.
  unfold ExtractedDigitBuffer in Hbuffer.
  destruct Hbuffer as [_ [_ [_ [Hdigits _]]]].
  specialize (Hdigits i ltac:(lia)).
  subst power_ll.
  assert (Hpowpos : 0 < 10 ^ (i - 1)).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hanswer :
    signed_last_nbits
      (Z.rem
        (ans +
         Z.rem
           (Z.rem (Z.rem x_pre (10 ^ (i - 1)) + 1) 1000000007 *
            Z.rem (Z.quot x_pre (10 ^ (i - 1))) 10)
           1000000007)
        1000000007) 32 =
    (answer_before + choice_sum +
      (((x_pre mod 10 ^ (i - 1)) + 1) mod digit_sum_modulus) *
        Znth i digits_l_2 0) mod digit_sum_modulus).
  {
    rewrite (Z.rem_mod_nonneg x_pre (10 ^ (i - 1))) by lia.
    rewrite (Z.quot_div_nonneg x_pre (10 ^ (i - 1))) by lia.
    assert (Hdivnonneg : 0 <= x_pre / 10 ^ (i - 1)).
    { apply Z.div_pos; lia. }
    rewrite (Z.rem_mod_nonneg (x_pre / 10 ^ (i - 1)) 10) by lia.
    pose proof (Z.mod_pos_bound x_pre (10 ^ (i - 1)) Hpowpos)
      as Hxmod.
    rewrite (Z.rem_mod_nonneg
      (x_pre mod 10 ^ (i - 1) + 1) 1000000007) by lia.
    rewrite (Z.rem_mod_nonneg
      (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007) *
       ((x_pre / 10 ^ (i - 1)) mod 10)) 1000000007).
    2: {
      pose proof (Z.mod_pos_bound
        (x_pre mod 10 ^ (i - 1) + 1) 1000000007 ltac:(lia))
        as Hlowmod.
      pose proof (Z.mod_pos_bound
        (x_pre / 10 ^ (i - 1)) 10 ltac:(lia)) as Hdigitmod.
      nia.
    }
    rewrite (Z.rem_mod_nonneg
      (ans +
       (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007 *
         ((x_pre / 10 ^ (i - 1)) mod 10)) mod 1000000007))
      1000000007).
    2: {
      pose proof (Z.mod_pos_bound
        (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007 *
          ((x_pre / 10 ^ (i - 1)) mod 10)))
        1000000007 ltac:(lia)).
      lia.
    }
    unfold digit_sum_modulus in *.
    pose proof (Z.mod_pos_bound
      (ans +
        (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007 *
          ((x_pre / 10 ^ (i - 1)) mod 10)) mod 1000000007))
      1000000007 ltac:(lia)) as Houtermod.
    replace
      (signed_last_nbits
        ((ans +
          (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007 *
            ((x_pre / 10 ^ (i - 1)) mod 10)) mod 1000000007))
         mod 1000000007) 32)
      with
      ((ans +
        (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007 *
          ((x_pre / 10 ^ (i - 1)) mod 10)) mod 1000000007))
       mod 1000000007).
    2: {
      symmetry.
      apply signed_last_nbits_eq.
      - lia.
      - change (-2147483648 <=
          (ans +
            (((x_pre mod 10 ^ (i - 1) + 1) mod 1000000007 *
              ((x_pre / 10 ^ (i - 1)) mod 10)) mod 1000000007))
            mod 1000000007 < 2147483648).
        lia.
    }
    rewrite Hdigits.
    rewrite HansEq.
    rewrite Z.add_mod_idemp_l by lia.
    repeat rewrite Z.add_mod_idemp_r by lia.
    reflexivity.
    all: try lia.
  }
  rewrite Hanswer.
  exact Hsemantic.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_10_split_goal_3 : prefix_digits_sum_entail_wit_10_split_goal_3.
Proof.
  aggressive_pre_process.
  eapply outer_progress_predecessor__prefix_inner_outer_scan.
  - exact PreH1.
  - exact PreH2.
  - exact PreH5.
  - exact PreH6.
  - exact PreH7.
  - lia.
  - exact PreH10.
  - exact PreH11.
  - lia.
  - exact PreH14.
  - exact PreH15.
  - exact PreH16.
  - exact PreH18.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_10_split_goal_4 : prefix_digits_sum_entail_wit_10_split_goal_4.
Proof.
  aggressive_pre_process.
  assert (Hpower_pos : 0 < power_ll).
  {
    unfold OuterDigitPositionPower in PreH18.
    destruct PreH18 as [[Hi Hpower] | [[Hlo Hhi] Hpower]].
    - lia.
    - subst power_ll.
      apply Z.pow_pos_nonneg; lia.
  }
  pose proof (Z.rem_bound_pos_pos x_pre power_ll Hpower_pos ltac:(lia))
    as Hx_rem.
  pose proof (Z.rem_bound_pos_pos
    (Z.rem x_pre power_ll + 1) 1000000007 ltac:(lia) ltac:(lia))
    as Hlower_digits.
  assert (Hquot_nonnegative : 0 <= Z.quot x_pre power_ll).
  {
    apply Z.quot_pos; lia.
  }
  pose proof (Z.rem_bound_pos_pos
    (Z.quot x_pre power_ll) 10 ltac:(lia) Hquot_nonnegative)
    as Hcurrent_digit.
  pose proof (Z.rem_bound_pos_pos
    (Z.rem (Z.rem x_pre power_ll + 1) 1000000007 *
     Z.rem (Z.quot x_pre power_ll) 10)
    1000000007 ltac:(lia) ltac:(nia))
    as Hmoving.
  pose proof (Z.rem_bound_pos_pos
    (ans +
     Z.rem
       (Z.rem (Z.rem x_pre power_ll + 1) 1000000007 *
        Z.rem (Z.quot x_pre power_ll) 10)
       1000000007)
    1000000007 ltac:(lia) ltac:(lia))
    as Hanswer.
  rewrite signed_last_nbits_small.
  - lia.
  - lia.
  - change
      (0 <=
       Z.rem
         (ans +
          Z.rem
            (Z.rem (Z.rem x_pre power_ll + 1) 1000000007 *
             Z.rem (Z.quot x_pre power_ll) 10)
            1000000007)
         1000000007 < 2147483648).
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_10_split_goal_5 : prefix_digits_sum_entail_wit_10_split_goal_5.
Proof.
  aggressive_pre_process.
  assert (Hpower_pos : 0 < power_ll).
  {
    unfold OuterDigitPositionPower in PreH18.
    destruct PreH18 as [[Hi Hpower] | [[Hlo Hhi] Hpower]].
    - lia.
    - subst power_ll.
      apply Z.pow_pos_nonneg; lia.
  }
  pose proof (Z.rem_bound_pos_pos x_pre power_ll Hpower_pos ltac:(lia))
    as Hx_rem.
  pose proof (Z.rem_bound_pos_pos
    (Z.rem x_pre power_ll + 1) 1000000007 ltac:(lia) ltac:(lia))
    as Hlower_digits.
  assert (Hquot_nonnegative : 0 <= Z.quot x_pre power_ll).
  {
    apply Z.quot_pos; lia.
  }
  pose proof (Z.rem_bound_pos_pos
    (Z.quot x_pre power_ll) 10 ltac:(lia) Hquot_nonnegative)
    as Hcurrent_digit.
  pose proof (Z.rem_bound_pos_pos
    (Z.rem (Z.rem x_pre power_ll + 1) 1000000007 *
     Z.rem (Z.quot x_pre power_ll) 10)
    1000000007 ltac:(lia) ltac:(nia))
    as Hmoving.
  pose proof (Z.rem_bound_pos_pos
    (ans +
     Z.rem
       (Z.rem (Z.rem x_pre power_ll + 1) 1000000007 *
        Z.rem (Z.quot x_pre power_ll) 10)
       1000000007)
    1000000007 ltac:(lia) ltac:(lia))
    as Hanswer.
  rewrite signed_last_nbits_small.
  - lia.
  - lia.
  - change
      (0 <=
       Z.rem
         (ans +
          Z.rem
            (Z.rem (Z.rem x_pre power_ll + 1) 1000000007 *
             Z.rem (Z.quot x_pre power_ll) 10)
            1000000007)
         1000000007 < 2147483648).
    lia.
Qed.

Lemma proof_of_prefix_digits_sum_entail_wit_10 : prefix_digits_sum_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_10_split_goal_4.
  - Goal_apply proof_of_prefix_digits_sum_entail_wit_10_split_goal_5.
Qed.

Lemma proof_of_prefix_digits_sum_return_wit_1_split_goal_1 : prefix_digits_sum_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  unfold AccumulatedDigitSumCorrect in PreH13.
  destruct PreH13 as [[Hi Hprefix_sum] | [Hi Hremaining]].
  - exact Hprefix_sum.
  - lia.
Qed.

Lemma proof_of_prefix_digits_sum_return_wit_1_split_goal_spatial : prefix_digits_sum_return_wit_1_split_goal_spatial.
Proof.
  aggressive_pre_process.
  sep_apply (IntArray.full_to_undef_full digits_pre 20 digits_l); easy.
Qed.

Lemma proof_of_prefix_digits_sum_return_wit_1 : prefix_digits_sum_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_prefix_digits_sum_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_prefix_digits_sum_return_wit_2_split_goal_1 : prefix_digits_sum_return_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  apply PrefixDigitSum_nonpositive.
  lia.
Qed.

Lemma proof_of_prefix_digits_sum_return_wit_2 : prefix_digits_sum_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prefix_digits_sum_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_interval_digits_sum_safety_wit_4_split_goal_1 : interval_digits_sum_safety_wit_4_split_goal_1.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  pose proof (Z.rem_bound_abs (retval - retval_2) digit_sum_modulus
    ltac:(unfold digit_sum_modulus; lia)) as Hrem.
  apply Z.abs_lt in Hrem.
  unfold digit_sum_modulus in *.
  lia.
Qed.

Lemma proof_of_interval_digits_sum_safety_wit_4_split_goal_2 : interval_digits_sum_safety_wit_4_split_goal_2.
Proof.
  aggressive_pre_process.
  split_pures; dump_pre_spatial.
  pose proof (Z.rem_bound_abs (retval - retval_2) digit_sum_modulus
    ltac:(unfold digit_sum_modulus; lia)) as Hrem.
  apply Z.abs_lt in Hrem.
  unfold digit_sum_modulus in *.
  lia.
Qed.

Lemma proof_of_interval_digits_sum_safety_wit_4 : interval_digits_sum_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_interval_digits_sum_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_interval_digits_sum_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_interval_digits_sum_return_wit_1_split_goal_1 : interval_digits_sum_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  rewrite normalized_outer_rem__interval_bridge.
  apply interval_answer_upper__interval_bridge.
Qed.

Lemma proof_of_interval_digits_sum_return_wit_1_split_goal_2 : interval_digits_sum_return_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  rewrite normalized_outer_rem__interval_bridge.
  apply interval_answer_lower__interval_bridge.
Qed.

Lemma proof_of_interval_digits_sum_return_wit_1_split_goal_3 : interval_digits_sum_return_wit_1_split_goal_3.
Proof.
  aggressive_pre_process.
  rewrite normalized_outer_rem__interval_bridge.
  apply IntervalDigitSum_from_prefixes__interval_bridge; assumption.
Qed.

Lemma proof_of_interval_digits_sum_return_wit_1 : interval_digits_sum_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_interval_digits_sum_return_wit_1_split_goal_1.
  - Goal_apply proof_of_interval_digits_sum_return_wit_1_split_goal_2.
  - Goal_apply proof_of_interval_digits_sum_return_wit_1_split_goal_3.
Qed.
