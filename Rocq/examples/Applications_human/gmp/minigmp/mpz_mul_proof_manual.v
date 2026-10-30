From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_mul_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_mul_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_mul_safety_wit_46_r_eq_op2_split_goal_1 : mpz_mul_safety_wit_46_r_eq_op2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2)
    (Zabs size_2) (Zabs size)).
  Intros_p Hsum.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_46_r_eq_op2_split_goal_2 : mpz_mul_safety_wit_46_r_eq_op2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_46_r_eq_op2 : mpz_mul_safety_wit_46_r_eq_op2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_46_r_eq_op2_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_46_r_eq_op2_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_47_r_eq_op1_split_goal_1 : mpz_mul_safety_wit_47_r_eq_op1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_47_r_eq_op1_split_goal_2 : mpz_mul_safety_wit_47_r_eq_op1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: intros; Intros; dump_pre_spatial; subst;
    pose proof (Z.abs_nonneg size);
    pose proof (Z.abs_nonneg size_2); lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_47_r_eq_op1 : mpz_mul_safety_wit_47_r_eq_op1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_47_r_eq_op1_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_47_r_eq_op1_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_48_neq_split_goal_1 : mpz_mul_safety_wit_48_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr ptr_2 (Zabs z1_neq) (Zabs z2_neq) (Zabs size) (Zabs size_2)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_48_neq_split_goal_2 : mpz_mul_safety_wit_48_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_48_neq : mpz_mul_safety_wit_48_neq.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_48_neq_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_48_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_49_r_eq_op2_split_goal_1 : mpz_mul_safety_wit_49_r_eq_op2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2)
    (Zabs size_2) (Zabs size)).
  Intros_p Hsum.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_49_r_eq_op2_split_goal_2 : mpz_mul_safety_wit_49_r_eq_op2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_49_r_eq_op2 : mpz_mul_safety_wit_49_r_eq_op2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_49_r_eq_op2_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_49_r_eq_op2_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_50_r_eq_op1_split_goal_1 : mpz_mul_safety_wit_50_r_eq_op1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_50_r_eq_op1_split_goal_2 : mpz_mul_safety_wit_50_r_eq_op1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: intros; Intros; dump_pre_spatial; subst;
    pose proof (Z.abs_nonneg size);
    pose proof (Z.abs_nonneg size_2); lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_50_r_eq_op1 : mpz_mul_safety_wit_50_r_eq_op1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_50_r_eq_op1_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_50_r_eq_op1_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_51_neq_split_goal_1 : mpz_mul_safety_wit_51_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr ptr_2 (Zabs z1_neq) (Zabs z2_neq) (Zabs size) (Zabs size_2)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_51_neq_split_goal_2 : mpz_mul_safety_wit_51_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_51_neq : mpz_mul_safety_wit_51_neq.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_51_neq_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_51_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_52_r_eq_op2_split_goal_1 : mpz_mul_safety_wit_52_r_eq_op2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2)
    (Zabs size_2) (Zabs size)).
  Intros_p Hsum.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_52_r_eq_op2_split_goal_2 : mpz_mul_safety_wit_52_r_eq_op2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_52_r_eq_op2 : mpz_mul_safety_wit_52_r_eq_op2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_52_r_eq_op2_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_52_r_eq_op2_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_53_r_eq_op1_split_goal_1 : mpz_mul_safety_wit_53_r_eq_op1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_53_r_eq_op1_split_goal_2 : mpz_mul_safety_wit_53_r_eq_op1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: intros; Intros; dump_pre_spatial; subst;
    pose proof (Z.abs_nonneg size);
    pose proof (Z.abs_nonneg size_2); lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_53_r_eq_op1 : mpz_mul_safety_wit_53_r_eq_op1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_53_r_eq_op1_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_53_r_eq_op1_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_54_neq_split_goal_1 : mpz_mul_safety_wit_54_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr ptr_2 (Zabs z1_neq) (Zabs z2_neq) (Zabs size) (Zabs size_2)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_54_neq_split_goal_2 : mpz_mul_safety_wit_54_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_54_neq : mpz_mul_safety_wit_54_neq.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_54_neq_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_54_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_55_r_eq_op2_split_goal_1 : mpz_mul_safety_wit_55_r_eq_op2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2)
    (Zabs size_2) (Zabs size)).
  Intros_p Hsum.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_55_r_eq_op2_split_goal_2 : mpz_mul_safety_wit_55_r_eq_op2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_55_r_eq_op2 : mpz_mul_safety_wit_55_r_eq_op2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_55_r_eq_op2_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_55_r_eq_op2_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_56_r_eq_op1_split_goal_1 : mpz_mul_safety_wit_56_r_eq_op1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_56_r_eq_op1_split_goal_2 : mpz_mul_safety_wit_56_r_eq_op1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: intros; Intros; dump_pre_spatial; subst;
    pose proof (Z.abs_nonneg size);
    pose proof (Z.abs_nonneg size_2); lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_56_r_eq_op1 : mpz_mul_safety_wit_56_r_eq_op1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_56_r_eq_op1_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_56_r_eq_op1_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_safety_wit_57_neq_split_goal_1 : mpz_mul_safety_wit_57_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr ptr_2 (Zabs z1_neq) (Zabs z2_neq) (Zabs size) (Zabs size_2)).
  Intros.
  subst retval retval_2.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_57_neq_split_goal_2 : mpz_mul_safety_wit_57_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_safety_wit_57_neq : mpz_mul_safety_wit_57_neq.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_safety_wit_57_neq_split_goal_1.
  - Goal_apply proof_of_mpz_mul_safety_wit_57_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_1_neq : mpz_mul_entail_wit_1_1_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1_neq z2_neq size size_2 cap cap_2
    PreH10 PreH9 PreH8 PreH7).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1_neq /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2_neq /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_2_neq : mpz_mul_entail_wit_1_2_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1_neq z2_neq size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1_neq /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2_neq /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_3_neq : mpz_mul_entail_wit_1_3_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1_neq z2_neq size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1_neq /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2_neq /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_4_neq : mpz_mul_entail_wit_1_4_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1_neq z2_neq size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1_neq /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2_neq /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_2_1_r_eq_op1 : mpz_mul_entail_wit_2_1_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op1) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op1) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap_2 ptr_2 data_op2 data_op1 cap cap size ptr ptr size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op1 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op1 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_2_2_r_eq_op1 : mpz_mul_entail_wit_2_2_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op1) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op1) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap_2 ptr_2 data_op2 data_op1 cap cap size ptr ptr size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op1 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op1 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_2_3_r_eq_op1 : mpz_mul_entail_wit_2_3_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op1) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op1) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap_2 ptr_2 data_op2 data_op1 cap cap size ptr ptr size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op1 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op1 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_2_4_r_eq_op1 : mpz_mul_entail_wit_2_4_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op1) (Zabs z1_r_eq_op1) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op1) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op1) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap_2 ptr_2 data_op2 data_op1 cap cap size ptr ptr size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op1 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op1 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_3_1_r_eq_op2 : mpz_mul_entail_wit_3_1_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op2) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op2) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap ptr data_op2 data_op1 cap_2 cap_2 size_2 ptr_2 ptr_2 size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op2 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op2 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_3_2_r_eq_op2 : mpz_mul_entail_wit_3_2_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op2) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op2) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap ptr data_op2 data_op1 cap_2 cap_2 size_2 ptr_2 ptr_2 size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op2 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op2 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_3_3_r_eq_op2 : mpz_mul_entail_wit_3_3_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op2) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op2) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap ptr data_op2 data_op1 cap_2 cap_2 size_2 ptr_2 ptr_2 size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op2 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op2 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_3_4_r_eq_op2 : mpz_mul_entail_wit_3_4_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    ptr_2 ptr (Zabs z2_r_eq_op2) (Zabs z1_r_eq_op2) (Zabs size_2) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs z2_r_eq_op2) (Zabs size_2)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z1_r_eq_op2) (Zabs size)).
  Intros.
  prop_apply (store_int_range (&(op2_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap_2).
  Intros.
  prop_apply (store_int_range (&(op1_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data_op1 data_op2.
  Exists cap ptr data_op2 data_op1 cap_2 cap_2 size_2 ptr_2 ptr_2 size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_op1 = Zabs z1_r_eq_op2 /\ last data_op1 1 >= 1 /\ list_within_bound UINT_MOD data_op1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_op2 = Zabs z2_r_eq_op2 /\ last data_op2 1 >= 1 /\ list_within_bound UINT_MOD data_op2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  split_pure_spatial.
  - match goal with H: Zabs size = Zlength data_op1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_op2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_5_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_5_r_eq_op1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_entail_wit_5_r_eq_op1 : mpz_mul_entail_wit_5_r_eq_op1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_entail_wit_5_r_eq_op1_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_entail_wit_6_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_6_r_eq_op2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_entail_wit_6_r_eq_op2 : mpz_mul_entail_wit_6_r_eq_op2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_entail_wit_6_r_eq_op2_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_entail_wit_7_neq_split_goal_spatial : mpz_mul_entail_wit_7_neq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (vn + un) with (un + vn) by lia.
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_7_neq : mpz_mul_entail_wit_7_neq.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_entail_wit_7_neq_split_goal_spatial.
Qed.

Lemma proof_of_mpz_mul_entail_wit_8_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_8_r_eq_op1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_entail_wit_8_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_8_r_eq_op1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  replace (vn + un) with (un + vn) by lia;
  cancel (UIntArray.undef_full rp (un + vn)).
Qed.

Lemma proof_of_mpz_mul_entail_wit_8_r_eq_op1 : mpz_mul_entail_wit_8_r_eq_op1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_entail_wit_8_r_eq_op1_split_goal_spatial.
  - Goal_apply proof_of_mpz_mul_entail_wit_8_r_eq_op1_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_entail_wit_9_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_9_r_eq_op2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_entail_wit_9_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_9_r_eq_op2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (vn + un) with (un + vn) by lia.
  cancel (UIntArray.undef_full rp (un + vn)).
Qed.

Lemma proof_of_mpz_mul_entail_wit_9_r_eq_op2 : mpz_mul_entail_wit_9_r_eq_op2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_entail_wit_9_r_eq_op2_split_goal_spatial.
  Goal_apply proof_of_mpz_mul_entail_wit_9_r_eq_op2_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_1_neq_split_goal_1 : mpz_mul_entail_wit_10_1_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_1_neq_split_goal_2 : mpz_mul_entail_wit_10_1_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_1_neq_split_goal_3 : mpz_mul_entail_wit_10_1_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_1_neq_split_goal_4 : mpz_mul_entail_wit_10_1_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_1_neq_split_goal_spatial : mpz_mul_entail_wit_10_1_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_1_neq : mpz_mul_entail_wit_10_1_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1_neq l2_neq l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l1_neq,
      Hlast: last l1_neq 1 >= 1,
      Hlen: Zlength l1_neq = un,
      Hval: list_to_Z UINT_MOD l1_neq = Zabs z1_neq |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l2_neq,
      Hlast: last l2_neq 1 >= 1,
      Hlen: Zlength l2_neq = vn,
      Hval: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_2_neq_split_goal_1 : mpz_mul_entail_wit_10_2_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_2_neq_split_goal_2 : mpz_mul_entail_wit_10_2_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_2_neq_split_goal_3 : mpz_mul_entail_wit_10_2_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_2_neq_split_goal_4 : mpz_mul_entail_wit_10_2_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_2_neq_split_goal_spatial : mpz_mul_entail_wit_10_2_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_2_neq : mpz_mul_entail_wit_10_2_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2_neq l1_neq l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_3_neq_split_goal_1 : mpz_mul_entail_wit_10_3_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_3_neq_split_goal_2 : mpz_mul_entail_wit_10_3_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_3_neq_split_goal_3 : mpz_mul_entail_wit_10_3_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_3_neq_split_goal_4 : mpz_mul_entail_wit_10_3_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_3_neq_split_goal_spatial : mpz_mul_entail_wit_10_3_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_3_neq : mpz_mul_entail_wit_10_3_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply_p (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply_p (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  sepcon_right_assoc.
  cancel.
  rewrite (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  rewrite (store_int_undef_store_int &("rn") (-(un + vn))).
  rewrite (store_int_undef_store_int &("un") un).
  rewrite (store_int_undef_store_int &("vn") vn).
  rewrite (store_int_undef_store_int &("sign") 1).
  rewrite (store_ptr_undef_store_ptr &("rp") rp).
  rewrite (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  rewrite (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  rewrite (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  sepcon_right_assoc.
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_4_neq_split_goal_1 : mpz_mul_entail_wit_10_4_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_4_neq_split_goal_2 : mpz_mul_entail_wit_10_4_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_4_neq_split_goal_3 : mpz_mul_entail_wit_10_4_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_4_neq_split_goal_4 : mpz_mul_entail_wit_10_4_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_4_neq_split_goal_spatial : mpz_mul_entail_wit_10_4_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_4_neq : mpz_mul_entail_wit_10_4_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply_p (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply_p (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  sepcon_right_assoc.
  cancel.
  rewrite (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  rewrite (store_int_undef_store_int &("rn") (-(un + vn))).
  rewrite (store_int_undef_store_int &("un") un).
  rewrite (store_int_undef_store_int &("vn") vn).
  rewrite (store_int_undef_store_int &("sign") 1).
  rewrite (store_ptr_undef_store_ptr &("rp") rp).
  rewrite (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  rewrite (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  rewrite (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  sepcon_right_assoc.
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_5_neq_split_goal_1 : mpz_mul_entail_wit_10_5_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_5_neq_split_goal_2 : mpz_mul_entail_wit_10_5_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_5_neq_split_goal_3 : mpz_mul_entail_wit_10_5_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_5_neq_split_goal_4 : mpz_mul_entail_wit_10_5_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_5_neq_split_goal_spatial : mpz_mul_entail_wit_10_5_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_5_neq : mpz_mul_entail_wit_10_5_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1_neq l2_neq l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_neq op2size_neq).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_6_neq_split_goal_1 : mpz_mul_entail_wit_10_6_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_6_neq_split_goal_2 : mpz_mul_entail_wit_10_6_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_6_neq_split_goal_3 : mpz_mul_entail_wit_10_6_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_6_neq_split_goal_4 : mpz_mul_entail_wit_10_6_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_6_neq_split_goal_spatial : mpz_mul_entail_wit_10_6_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_6_neq : mpz_mul_entail_wit_10_6_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2_neq l1_neq l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_neq op2size_neq).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_7_neq_split_goal_1 : mpz_mul_entail_wit_10_7_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_7_neq_split_goal_2 : mpz_mul_entail_wit_10_7_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_7_neq_split_goal_3 : mpz_mul_entail_wit_10_7_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_7_neq_split_goal_4 : mpz_mul_entail_wit_10_7_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_7_neq_split_goal_spatial : mpz_mul_entail_wit_10_7_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_7_neq : mpz_mul_entail_wit_10_7_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_neq op2size_neq).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply_p (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply_p (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  sepcon_right_assoc.
  cancel.
  rewrite (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  rewrite (store_int_undef_store_int &("rn") (un + vn)).
  rewrite (store_int_undef_store_int &("un") un).
  rewrite (store_int_undef_store_int &("vn") vn).
  rewrite (store_int_undef_store_int &("sign") 0).
  rewrite (store_ptr_undef_store_ptr &("rp") rp).
  rewrite (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  rewrite (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  rewrite (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  sepcon_right_assoc.
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_10_8_neq_split_goal_1 : mpz_mul_entail_wit_10_8_neq_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_8_neq_split_goal_2 : mpz_mul_entail_wit_10_8_neq_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_8_neq_split_goal_3 : mpz_mul_entail_wit_10_8_neq_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_8_neq_split_goal_4 : mpz_mul_entail_wit_10_8_neq_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_8_neq_split_goal_spatial : mpz_mul_entail_wit_10_8_neq_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_10_8_neq : mpz_mul_entail_wit_10_8_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_neq * z2_neq)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_neq * list_to_Z UINT_MOD l2_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2_neq * list_to_Z UINT_MOD l1_neq,
      Hl1: list_to_Z UINT_MOD l1_neq = Zabs z1_neq,
      Hl2: list_to_Z UINT_MOD l2_neq = Zabs z2_neq |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_neq * z2_neq)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_neq) un).
  { eapply (is_compact_Z_from_full_last l1_neq); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_neq) vn).
  { eapply (is_compact_Z_from_full_last l2_neq); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_neq PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_neq).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_neq PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_neq op2size_neq).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_neq * z2_neq) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply_p (UIntArray.undef_seg_valid op1ptr_neq un op1cap_neq).
  Intros.
  prop_apply_p (UIntArray.undef_seg_valid op2ptr_neq vn op2cap_neq).
  Intros.
  unfold store_Z.
  Exists rptr_neq rsize_neq rcap_neq op1ptr_neq op1size_neq op1cap_neq op2ptr_neq op2size_neq op2cap_neq rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_neq) with un by lia.
  replace (Zabs op2size_neq) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  sepcon_right_assoc.
  cancel.
  rewrite (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_neq * z2_neq))); try assumption; try lia.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op1ptr_neq un l1_neq (Zabs z1_neq)); try assumption.
  rewrite (UIntArray_full_to_mpd_store_Z_compact op2ptr_neq vn l2_neq (Zabs z2_neq)); try assumption.
  rewrite (store_int_undef_store_int &("rn") (un + vn)).
  rewrite (store_int_undef_store_int &("un") un).
  rewrite (store_int_undef_store_int &("vn") vn).
  rewrite (store_int_undef_store_int &("sign") 0).
  rewrite (store_ptr_undef_store_ptr &("rp") rp).
  rewrite (store_ptr_undef_store_ptr &("up") op1ptr_neq).
  rewrite (store_ptr_undef_store_ptr &("vp") op2ptr_neq).
  rewrite (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  sepcon_right_assoc.
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_1_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_1_r_eq_op1 : mpz_mul_entail_wit_11_1_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1_r_eq_op1 l2_r_eq_op1 l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l1_r_eq_op1,
      Hlast: last l1_r_eq_op1 1 >= 1,
      Hlen: Zlength l1_r_eq_op1 = un,
      Hval: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1 |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l2_r_eq_op1,
      Hlast: last l2_r_eq_op1 1 >= 1,
      Hlen: Zlength l2_r_eq_op1 = vn,
      Hval: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_2_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_2_r_eq_op1 : mpz_mul_entail_wit_11_2_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2_r_eq_op1 l1_r_eq_op1 l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_3_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_3_r_eq_op1 : mpz_mul_entail_wit_11_3_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  split_pure_spatial.
  - repeat rewrite sepcon_right_assoc.
    cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_4_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_4_r_eq_op1 : mpz_mul_entail_wit_11_4_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  split_pure_spatial.
  - repeat rewrite sepcon_right_assoc.
    cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_5_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_5_r_eq_op1 : mpz_mul_entail_wit_11_5_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1_r_eq_op1 l2_r_eq_op1 l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op1 op2size_r_eq_op1).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_6_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_6_r_eq_op1 : mpz_mul_entail_wit_11_6_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2_r_eq_op1 l1_r_eq_op1 l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op1 op2size_r_eq_op1).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_7_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_7_r_eq_op1 : mpz_mul_entail_wit_11_7_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op1 op2size_r_eq_op1).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  split_pure_spatial.
  - repeat rewrite sepcon_right_assoc.
    cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_1 : mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_2 : mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_3 : mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_4 : mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_spatial : mpz_mul_entail_wit_11_8_r_eq_op1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_11_8_r_eq_op1 : mpz_mul_entail_wit_11_8_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op1 * z2_r_eq_op1)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op1 * list_to_Z UINT_MOD l2_r_eq_op1,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op1 = Zabs z1_r_eq_op1,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op1 = Zabs z2_r_eq_op1 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op1 * z2_r_eq_op1)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op1) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op1) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op1); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op1 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op1 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op1 op2size_r_eq_op1).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op1 * z2_r_eq_op1) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op1 un op1cap_r_eq_op1).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op1 vn op2cap_r_eq_op1).
  Intros.
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op1 op1size_r_eq_op1 op1cap_r_eq_op1 op2ptr_r_eq_op1 op2size_r_eq_op1 op2cap_r_eq_op1 rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op1) with un by lia.
  replace (Zabs op2size_r_eq_op1) with vn by lia.
  split_pure_spatial.
  - repeat rewrite sepcon_right_assoc.
    cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op1 * z2_r_eq_op1))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op1 un l1_r_eq_op1 (Zabs z1_r_eq_op1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op1 vn l2_r_eq_op1 (Zabs z2_r_eq_op1)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op1).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op1).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_1_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_1_r_eq_op2 : mpz_mul_entail_wit_12_1_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1_r_eq_op2 l2_r_eq_op2 l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l1_r_eq_op2,
      Hlast: last l1_r_eq_op2 1 >= 1,
      Hlen: Zlength l1_r_eq_op2 = un,
      Hval: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2 |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l2_r_eq_op2,
      Hlast: last l2_r_eq_op2 1 >= 1,
      Hlen: Zlength l2_r_eq_op2 = vn,
      Hval: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_2_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_2_r_eq_op2 : mpz_mul_entail_wit_12_2_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2_r_eq_op2 l1_r_eq_op2 l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_3_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_3_r_eq_op2 : mpz_mul_entail_wit_12_3_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  repeat rewrite sepcon_right_assoc.
  cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_4_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_4_r_eq_op2 : mpz_mul_entail_wit_12_4_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH13.
    destruct PreH13 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  repeat rewrite sepcon_right_assoc.
  cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_5_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_5_r_eq_op2 : mpz_mul_entail_wit_12_5_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1_r_eq_op2 l2_r_eq_op2 l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op2 op2size_r_eq_op2).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_6_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_6_r_eq_op2 : mpz_mul_entail_wit_12_6_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2_r_eq_op2 l1_r_eq_op2 l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op2 op2size_r_eq_op2).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_7_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_7_r_eq_op2 : mpz_mul_entail_wit_12_7_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op2 op2size_r_eq_op2).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  repeat rewrite sepcon_right_assoc.
  cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  cancel.
Qed.

Lemma proof_of_mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_1 : mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_2 : mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_3 : mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_4 : mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_spatial : mpz_mul_entail_wit_12_8_r_eq_op2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mpz_mul_entail_wit_12_8_r_eq_op2 : mpz_mul_entail_wit_12_8_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1_r_eq_op2 * z2_r_eq_op2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1_r_eq_op2 * list_to_Z UINT_MOD l2_r_eq_op2,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = ?lhs * ?rhs,
      Hl1: list_to_Z UINT_MOD l1_r_eq_op2 = Zabs z1_r_eq_op2,
      Hl2: list_to_Z UINT_MOD l2_r_eq_op2 = Zabs z2_r_eq_op2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1_r_eq_op2 * z2_r_eq_op2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1_r_eq_op2) un).
  { eapply (is_compact_Z_from_full_last l1_r_eq_op2); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2_r_eq_op2) vn).
  { eapply (is_compact_Z_from_full_last l2_r_eq_op2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1_r_eq_op2 PreH29 PreH33) as [Hlo _]; rewrite PreH27 in Hlo; rewrite PreH31 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2_r_eq_op2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2_r_eq_op2 PreH30 PreH34) as [Hlo _]; rewrite PreH28 in Hlo; rewrite PreH32 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size_r_eq_op2 op2size_r_eq_op2).
  { unfold mpz_mul_sign in PreH13. destruct PreH13 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1_r_eq_op2 * z2_r_eq_op2) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr_r_eq_op2 un op1cap_r_eq_op2).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr_r_eq_op2 vn op2cap_r_eq_op2).
  Intros.
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  unfold store_Z.
  Exists op1ptr_r_eq_op2 op1size_r_eq_op2 op1cap_r_eq_op2 op2ptr_r_eq_op2 op2size_r_eq_op2 op2cap_r_eq_op2 rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size_r_eq_op2) with un by lia.
  replace (Zabs op2size_r_eq_op2) with vn by lia.
  split_pure_spatial.
  2: { repeat split_pures; dump_pre_spatial;
       try assumption; try reflexivity; try lia. }
  repeat rewrite sepcon_right_assoc.
  cancel.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1_r_eq_op2 * z2_r_eq_op2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr_r_eq_op2 un l1_r_eq_op2 (Zabs z1_r_eq_op2)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr_r_eq_op2 vn l2_r_eq_op2 (Zabs z2_r_eq_op2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr_r_eq_op2).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr_r_eq_op2).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  cancel.
Qed.

Lemma proof_of_mpz_mul_return_wit_1_r_eq_op2 : mpz_mul_return_wit_1_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre size.
  replace (Zabs 0) with 0 by lia.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z1_r_eq_op2)).
  Intros.
  assert (z1_r_eq_op2 = 0) by lia.
  subst z1_r_eq_op2.
  change (Zabs 0) with 0.
  rewrite Z.mul_0_l.
  sep_apply (store_Z_from_zero_fields op1_pre ptr cap ltac:(lia)).
  sep_apply (store_Z_zero_from_fields op2_pre ptr_2 size_2 cap_2 z2_r_eq_op2 ltac:(lia) ltac:(assumption)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_mpz_mul_return_wit_2_r_eq_op1 : mpz_mul_return_wit_2_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre size.
  replace (Zabs 0) with 0 by lia.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z1_r_eq_op1)).
  Intros.
  assert (z1_r_eq_op1 = 0) by lia.
  subst z1_r_eq_op1.
  change (Zabs 0) with 0.
  rewrite Z.mul_0_l.
  sep_apply (store_Z_from_zero_fields op1_pre ptr cap ltac:(lia)).
  sep_apply (store_Z_from_fields op2_pre ptr_2 size_2 cap_2 z2_r_eq_op1 ltac:(lia) ltac:(assumption)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_mpz_mul_return_wit_3_neq_split_goal_1 : mpz_mul_return_wit_3_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_return_wit_3_neq_split_goal_2 : mpz_mul_return_wit_3_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z1_neq)).
  Intros_p Hz.
  assert (Hzero : z1_neq = 0) by lia.
  subst z1_neq.
  rewrite ?Z.mul_0_l, ?Z.mul_0_r.
  dump_pre_spatial. unfold same_sign. lia.
Qed.

Lemma proof_of_mpz_mul_return_wit_3_neq_split_goal_spatial : mpz_mul_return_wit_3_neq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z1_neq)).
  Intros_p Hz.
  assert (Hzero : z1_neq = 0) by lia.
  subst z1_neq.
  rewrite ?Z.mul_0_l, ?Z.mul_0_r.
  cbn [Z.abs].
  cancel (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs z2_neq) (Zabs size_2)).
  cancel (mpd_store_Z_compact UINT_MOD ptr 0 0).
  pose proof (Z.abs_nonneg size_3) as Hnonneg.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    ptr_3 (Zabs old_neq) (Zabs size_3) 0 cap_3
    Hnonneg PreH2 ltac:(lia) ltac:(lia)).
  Intros_p Hcompact.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.undef_full_empty, UIntArray.full_empty.
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try rewrite list_to_Z_nil; try rewrite Zlength_nil; simpl; auto; lia.
Qed.

Lemma proof_of_mpz_mul_return_wit_3_neq : mpz_mul_return_wit_3_neq.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_return_wit_3_neq_split_goal_spatial.
  - Goal_apply proof_of_mpz_mul_return_wit_3_neq_split_goal_1.
  - Goal_apply proof_of_mpz_mul_return_wit_3_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_return_wit_4_neq_split_goal_1 : mpz_mul_return_wit_4_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_return_wit_4_neq_split_goal_2 : mpz_mul_return_wit_4_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size_2.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs z2_neq)).
  Intros_p Hz.
  assert (Hzero : z2_neq = 0) by lia.
  subst z2_neq.
  rewrite ?Z.mul_0_l, ?Z.mul_0_r.
  dump_pre_spatial. unfold same_sign. lia.
Qed.

Lemma proof_of_mpz_mul_return_wit_4_neq_split_goal_spatial : mpz_mul_return_wit_4_neq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size_2.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs z2_neq)).
  Intros_p Hz.
  assert (Hzero : z2_neq = 0) by lia.
  subst z2_neq.
  rewrite ?Z.mul_0_l, ?Z.mul_0_r.
  cbn [Z.abs].
  cancel (mpd_store_Z_compact UINT_MOD ptr_2 0 0).
  cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs z1_neq) (Zabs size)).
  pose proof (Z.abs_nonneg size_3) as Hnonneg.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    ptr_3 (Zabs old_neq) (Zabs size_3) 0 cap_3
    Hnonneg PreH2 ltac:(lia) ltac:(lia)).
  Intros_p Hcompact.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.undef_full_empty, UIntArray.full_empty.
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try rewrite list_to_Z_nil; try rewrite Zlength_nil; simpl; auto; lia.
Qed.

Lemma proof_of_mpz_mul_return_wit_4_neq : mpz_mul_return_wit_4_neq.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_mul_return_wit_4_neq_split_goal_spatial.
  - Goal_apply proof_of_mpz_mul_return_wit_4_neq_split_goal_1.
  - Goal_apply proof_of_mpz_mul_return_wit_4_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_mul_return_wit_5_r_eq_op1 : mpz_mul_return_wit_5_r_eq_op1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre size_2.
  replace (Zabs 0) with 0 by lia.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs z2_r_eq_op1)).
  Intros.
  assert (z2_r_eq_op1 = 0) by lia.
  subst z2_r_eq_op1.
  change (Zabs 0) with 0.
  rewrite Z.mul_0_r.
  sep_apply (store_Z_zero_from_fields op1_pre ptr size cap z1_r_eq_op1 ltac:(lia) ltac:(assumption)).
  sep_apply (store_Z_from_zero_fields op2_pre ptr_2 cap_2 ltac:(lia)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_mpz_mul_return_wit_6_r_eq_op2 : mpz_mul_return_wit_6_r_eq_op2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre size_2.
  replace (Zabs 0) with 0 by lia.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs z2_r_eq_op2)).
  Intros.
  assert (z2_r_eq_op2 = 0) by lia.
  subst z2_r_eq_op2.
  change (Zabs 0) with 0.
  rewrite Z.mul_0_r.
  sep_apply (store_Z_from_fields op1_pre ptr size cap z1_r_eq_op2 ltac:(lia) ltac:(assumption)).
  sep_apply (store_Z_from_zero_fields op2_pre ptr_2 cap_2 ltac:(lia)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_mpz_mul_return_wit_7_r_eq_op2_split_goal_spatial : mpz_mul_return_wit_7_r_eq_op2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst rop_pre.
  cancel.
Qed.

Lemma proof_of_mpz_mul_return_wit_7_r_eq_op2 : mpz_mul_return_wit_7_r_eq_op2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_return_wit_7_r_eq_op2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_mul_return_wit_8_r_eq_op1_split_goal_spatial : mpz_mul_return_wit_8_r_eq_op1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst rop_pre.
  cancel.
Qed.

Lemma proof_of_mpz_mul_return_wit_8_r_eq_op1 : mpz_mul_return_wit_8_r_eq_op1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_return_wit_8_r_eq_op1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_13_r_eq_op2_pure_split_goal_1 : mpz_mul_partial_solve_wit_13_r_eq_op2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_13_r_eq_op2_pure : mpz_mul_partial_solve_wit_13_r_eq_op2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_13_r_eq_op2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_14_r_eq_op1_pure_split_goal_1 : mpz_mul_partial_solve_wit_14_r_eq_op1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_14_r_eq_op1_pure : mpz_mul_partial_solve_wit_14_r_eq_op1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_14_r_eq_op1_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_15_neq_pure_split_goal_1 : mpz_mul_partial_solve_wit_15_neq_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_15_neq_pure : mpz_mul_partial_solve_wit_15_neq_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_15_neq_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_22_r_eq_op2_pure_split_goal_1 : mpz_mul_partial_solve_wit_22_r_eq_op2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_22_r_eq_op2_pure : mpz_mul_partial_solve_wit_22_r_eq_op2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_22_r_eq_op2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_23_r_eq_op1_pure_split_goal_1 : mpz_mul_partial_solve_wit_23_r_eq_op1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_23_r_eq_op1_pure : mpz_mul_partial_solve_wit_23_r_eq_op1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_23_r_eq_op1_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_24_neq_pure_split_goal_1 : mpz_mul_partial_solve_wit_24_neq_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_24_neq_pure : mpz_mul_partial_solve_wit_24_neq_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_24_neq_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_28_r_eq_op2_pure_split_goal_1 : mpz_mul_partial_solve_wit_28_r_eq_op2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_28_r_eq_op2_pure : mpz_mul_partial_solve_wit_28_r_eq_op2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_28_r_eq_op2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_29_r_eq_op1_pure_split_goal_1 : mpz_mul_partial_solve_wit_29_r_eq_op1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_29_r_eq_op1_pure : mpz_mul_partial_solve_wit_29_r_eq_op1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_29_r_eq_op1_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_30_neq_pure_split_goal_1 : mpz_mul_partial_solve_wit_30_neq_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_30_neq_pure : mpz_mul_partial_solve_wit_30_neq_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_30_neq_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_34_r_eq_op2_pure_split_goal_1 : mpz_mul_partial_solve_wit_34_r_eq_op2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_34_r_eq_op2_pure : mpz_mul_partial_solve_wit_34_r_eq_op2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_34_r_eq_op2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_35_r_eq_op1_pure_split_goal_1 : mpz_mul_partial_solve_wit_35_r_eq_op1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_35_r_eq_op1_pure : mpz_mul_partial_solve_wit_35_r_eq_op1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_35_r_eq_op1_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_36_neq_pure_split_goal_1 : mpz_mul_partial_solve_wit_36_neq_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_36_neq_pure : mpz_mul_partial_solve_wit_36_neq_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_36_neq_pure_split_goal_1.
Qed.

