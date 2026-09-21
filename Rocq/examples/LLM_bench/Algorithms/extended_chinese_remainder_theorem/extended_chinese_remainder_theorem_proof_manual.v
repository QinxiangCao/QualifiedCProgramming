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
From SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem Require Import extended_chinese_remainder_theorem_goal.
From SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem Require Import extended_chinese_remainder_theorem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib.
Require Import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib.
Local Open Scope sac.

Require Import AUXLib.MonotonicList.

(* Extract list domains from ownership before using the preserved arithmetic
   helpers. No input-range predicate is added to the public specification. *)
Ltac crt_prepare :=
  (LLM_pre_process ltac:(lia || int_auto));
  match goal with
  | |- context [IntArray.full ?ptr ?n ?xs] =>
    prop_apply (IntArray.full_Zlength ptr n xs)
  end; Intros;
  lazymatch goal with
  | HF : Forall2 Z.lt ?rs ?ms,
    HP : Forall (Z.lt 0) ?ms,
    HM : Forall (Z.ge 2147483647) ?ms,
    HR : Forall (Z.le 0) ?rs,
    HL : Zlength ?xs = ?n |- _ =>
    pose proof (proj1 (crt_forall2_Znth_iff Z.lt _ _) HF) as [Hsame_length2 Hlt2];
    pose proof (proj1 (Forall_Znth _ 0 _) HP) as Hpositive;
    pose proof (proj1 (Forall_Znth _ 0 _) HM) as Hmaximum;
    pose proof (proj1 (Forall_Znth _ 0 _) HR) as Hnonnegative;
    assert (Hinputs :
      1 <= n /\ Zlength rs = n /\ Zlength ms = n /\
      forall k, 0 <= k < n ->
        0 < Znth k ms 0 <= 2147483647 /\
        0 <= Znth k rs 0 < Znth k ms 0)
      by (split; [lia |]; split; [lia |]; split; [lia |];
          intros k Hk;
          specialize (Hpositive k ltac:(lia));
          specialize (Hmaximum k ltac:(lia));
          specialize (Hnonnegative k ltac:(lia));
          specialize (Hlt2 k ltac:(lia)); lia)
  end.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i Hinputs ltac:(lia))
    as [[Hmpos Hmmax] [Hrpos Hrmax]].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_9 : extended_chinese_remainder_theorem_safety_wit_9.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i Hinputs ltac:(lia))
    as [[Hmpos Hmmax] [Hrpos Hrmax]].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_14 : extended_chinese_remainder_theorem_safety_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm
    (retval_2 + Z.quot (Znth i modulus_values 0) retval)
    (Z.quot (Znth i modulus_values 0) retval)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_15 : extended_chinese_remainder_theorem_safety_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm
    (retval_2 + Z.quot (Znth i modulus_values 0) retval)
    (Z.quot (Znth i modulus_values 0) retval)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_16 : extended_chinese_remainder_theorem_safety_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm
    (retval_2 + Z.quot (Znth i modulus_values 0) retval)
    (Z.quot (Znth i modulus_values 0) retval)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_17 : extended_chinese_remainder_theorem_safety_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm
    (retval_2 + Z.quot (Znth i modulus_values 0) retval)
    (Z.quot (Znth i modulus_values 0) retval)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_18 : extended_chinese_remainder_theorem_safety_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm retval
    (Z.quot (Znth i modulus_values 0) retval_2)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_19 : extended_chinese_remainder_theorem_safety_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm retval
    (Z.quot (Znth i modulus_values 0) retval_2)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_20 : extended_chinese_remainder_theorem_safety_wit_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm retval
    (Z.quot (Znth i modulus_values 0) retval_2)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_21 : extended_chinese_remainder_theorem_safety_wit_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (bounded_merge_arithmetic__machine_bounds answer lcm retval
    (Z.quot (Znth i modulus_values 0) retval_2)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1.
Proof.
  crt_prepare.
  pose proof (crt_prefix_meaning_one__prefix_boundaries
    residue_values modulus_values n_pre Hinputs ltac:(lia)) as Hprefix.
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre 0 Hinputs ltac:(lia))
    as [[Hmpos Hmmax] [Hrpos Hrmax]].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_1 : extended_chinese_remainder_theorem_entail_wit_2_1.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i Hinputs ltac:(lia)) as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval ltac:(lia) PreH4 PreH3) as Hquotient.
  pose proof (crt_merge_difference_divisible__merge_transition
    residue_values modulus_values n_pre i answer lcm
    ltac:(lia) ltac:(lia) ltac:(eassumption) ltac:(eassumption) ltac:(lia))
    as Hdifference.
  rewrite <- PreH4 in Hdifference.
  assert (Hmodulus_divides : (retval | Znth i modulus_values 0)).
  { rewrite PreH4. apply Z.gcd_divide_r. }
  assert (Hmodulus_quot : Znth i modulus_values 0 ÷ retval =
      Znth i modulus_values 0 / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hdifference_quot : (Znth i residue_values 0 - answer) ÷ retval =
      (Znth i residue_values 0 - answer) / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  pose proof PreH2 as Hmul.
  unfold ModularMul in Hmul. destruct Hmul as [Hrange [q Hmul]].
  rewrite Hdifference_quot in Hmul.
  assert (Hmerge : CRTReducedMergeEquation answer lcm
    (Znth i residue_values 0) (Znth i modulus_values 0) (retval_2 + Znth i modulus_values 0 ÷ retval)).
  { eapply (reduced_merge_equation_from_bezout__merge_transition
      answer lcm (Znth i residue_values 0) (Znth i modulus_values 0)
      retval x_callee_v y_callee_v (retval_2 + Znth i modulus_values 0 ÷ retval) (q - 1));
      try eassumption.
    rewrite <- Hmodulus_quot. lia. }
  assert (Hstep : CRTLCMPrefix modulus_values (i + 1) =
    lcm * (Znth i modulus_values 0 ÷ retval)).
  { eapply crt_lcm_prefix_step__merge_transition;
      [exact Hinputs | lia | lia | eassumption | exact PreH4 | lia | exact Hmodulus_quot]. }
  match goal with
  | HS : forall count, 1 <= count <= n_pre -> _ |- _ =>
    pose proof (HS (i + 1) ltac:(lia)) as Hbound;
    rewrite Hstep in Hbound
  end.
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_2 : extended_chinese_remainder_theorem_entail_wit_2_2.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i Hinputs ltac:(lia)) as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval ltac:(lia) PreH4 PreH3) as Hquotient.
  pose proof (crt_merge_difference_divisible__merge_transition
    residue_values modulus_values n_pre i answer lcm
    ltac:(lia) ltac:(lia) ltac:(eassumption) ltac:(eassumption) ltac:(lia))
    as Hdifference.
  rewrite <- PreH4 in Hdifference.
  assert (Hmodulus_divides : (retval | Znth i modulus_values 0)).
  { rewrite PreH4. apply Z.gcd_divide_r. }
  assert (Hmodulus_quot : Znth i modulus_values 0 ÷ retval =
      Znth i modulus_values 0 / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hdifference_quot : (Znth i residue_values 0 - answer) ÷ retval =
      (Znth i residue_values 0 - answer) / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  pose proof PreH2 as Hmul.
  unfold ModularMul in Hmul. destruct Hmul as [Hrange [q Hmul]].
  rewrite Hdifference_quot in Hmul.
  assert (Hmerge : CRTReducedMergeEquation answer lcm
    (Znth i residue_values 0) (Znth i modulus_values 0) (retval_3 + Znth i modulus_values 0 ÷ retval)).
  { eapply (reduced_merge_equation_from_bezout__merge_transition
      answer lcm (Znth i residue_values 0) (Znth i modulus_values 0)
      retval x_callee_v_2 y_callee_v (retval_3 + Znth i modulus_values 0 ÷ retval) (q - 1));
      try eassumption.
    rewrite <- Hmodulus_quot. lia. }
  assert (Hstep : CRTLCMPrefix modulus_values (i + 1) =
    lcm * (Znth i modulus_values 0 ÷ retval)).
  { eapply crt_lcm_prefix_step__merge_transition;
      [exact Hinputs | lia | lia | eassumption | exact PreH4 | lia | exact Hmodulus_quot]. }
  match goal with
  | HS : forall count, 1 <= count <= n_pre -> _ |- _ =>
    pose proof (HS (i + 1) ltac:(lia)) as Hbound;
    rewrite Hstep in Hbound
  end.
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_3 : extended_chinese_remainder_theorem_entail_wit_2_3.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i Hinputs ltac:(lia)) as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval ltac:(lia) PreH4 PreH3) as Hquotient.
  pose proof (crt_merge_difference_divisible__merge_transition
    residue_values modulus_values n_pre i answer lcm
    ltac:(lia) ltac:(lia) ltac:(eassumption) ltac:(eassumption) ltac:(lia))
    as Hdifference.
  rewrite <- PreH4 in Hdifference.
  assert (Hmodulus_divides : (retval | Znth i modulus_values 0)).
  { rewrite PreH4. apply Z.gcd_divide_r. }
  assert (Hmodulus_quot : Znth i modulus_values 0 ÷ retval =
      Znth i modulus_values 0 / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hdifference_quot : (Znth i residue_values 0 - answer) ÷ retval =
      (Znth i residue_values 0 - answer) / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  pose proof PreH2 as Hmul.
  unfold ModularMul in Hmul. destruct Hmul as [Hrange [q Hmul]].
  rewrite Hdifference_quot in Hmul.
  assert (Hmerge : CRTReducedMergeEquation answer lcm
    (Znth i residue_values 0) (Znth i modulus_values 0) retval_2).
  { eapply (reduced_merge_equation_from_bezout__merge_transition
      answer lcm (Znth i residue_values 0) (Znth i modulus_values 0)
      retval x_callee_v y_callee_v retval_2 q);
      try eassumption.
    rewrite <- Hmodulus_quot. lia. }
  assert (Hstep : CRTLCMPrefix modulus_values (i + 1) =
    lcm * (Znth i modulus_values 0 ÷ retval)).
  { eapply crt_lcm_prefix_step__merge_transition;
      [exact Hinputs | lia | lia | eassumption | exact PreH4 | lia | exact Hmodulus_quot]. }
  match goal with
  | HS : forall count, 1 <= count <= n_pre -> _ |- _ =>
    pose proof (HS (i + 1) ltac:(lia)) as Hbound;
    rewrite Hstep in Hbound
  end.
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_4 : extended_chinese_remainder_theorem_entail_wit_2_4.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i Hinputs ltac:(lia)) as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval ltac:(lia) PreH4 PreH3) as Hquotient.
  pose proof (crt_merge_difference_divisible__merge_transition
    residue_values modulus_values n_pre i answer lcm
    ltac:(lia) ltac:(lia) ltac:(eassumption) ltac:(eassumption) ltac:(lia))
    as Hdifference.
  rewrite <- PreH4 in Hdifference.
  assert (Hmodulus_divides : (retval | Znth i modulus_values 0)).
  { rewrite PreH4. apply Z.gcd_divide_r. }
  assert (Hmodulus_quot : Znth i modulus_values 0 ÷ retval =
      Znth i modulus_values 0 / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hdifference_quot : (Znth i residue_values 0 - answer) ÷ retval =
      (Znth i residue_values 0 - answer) / retval).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  pose proof PreH2 as Hmul.
  unfold ModularMul in Hmul. destruct Hmul as [Hrange [q Hmul]].
  rewrite Hdifference_quot in Hmul.
  assert (Hmerge : CRTReducedMergeEquation answer lcm
    (Znth i residue_values 0) (Znth i modulus_values 0) retval_3).
  { eapply (reduced_merge_equation_from_bezout__merge_transition
      answer lcm (Znth i residue_values 0) (Znth i modulus_values 0)
      retval x_callee_v_2 y_callee_v retval_3 q);
      try eassumption.
    rewrite <- Hmodulus_quot. lia. }
  assert (Hstep : CRTLCMPrefix modulus_values (i + 1) =
    lcm * (Znth i modulus_values 0 ÷ retval)).
  { eapply crt_lcm_prefix_step__merge_transition;
      [exact Hinputs | lia | lia | eassumption | exact PreH4 | lia | exact Hmodulus_quot]. }
  match goal with
  | HS : forall count, 1 <= count <= n_pre -> _ |- _ =>
    pose proof (HS (i + 1) ltac:(lia)) as Hbound;
    rewrite Hstep in Hbound
  end.
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1.
Proof.
  crt_prepare.
  assert (Hnext : CRTPrefixMeaning residue_values modulus_values (i + 1)
    (answer + (retval_2 + Znth i modulus_values 0 ÷ retval) * lcm)
    (lcm * (Znth i modulus_values 0 ÷ retval))).
  { eapply crt_prefix_meaning_merge__merge_transition with (gcd := retval);
      try eassumption; try lia.
    apply quot_div_of_divide_pos__merge_transition; [lia |].
    match goal with HG : retval = Zgcd _ _ |- _ => rewrite HG end.
    apply Z.gcd_divide_r. }
  entailer_with ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2.
Proof.
  crt_prepare.
  assert (Hnext : CRTPrefixMeaning residue_values modulus_values (i + 1)
    (answer + (retval_2 + Znth i modulus_values 0 ÷ retval) * lcm)
    (lcm * (Znth i modulus_values 0 ÷ retval))).
  { eapply crt_prefix_meaning_merge__merge_transition with (gcd := retval);
      try eassumption; try lia.
    apply quot_div_of_divide_pos__merge_transition; [lia |].
    match goal with HG : retval = Zgcd _ _ |- _ => rewrite HG end.
    apply Z.gcd_divide_r. }
  entailer_with ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_3 : extended_chinese_remainder_theorem_entail_wit_3_3.
Proof.
  crt_prepare.
  assert (Hnext : CRTPrefixMeaning residue_values modulus_values (i + 1)
    (answer + retval_2 * lcm)
    (lcm * (Znth i modulus_values 0 ÷ retval))).
  { eapply crt_prefix_meaning_merge__merge_transition with (gcd := retval);
      try eassumption; try lia.
    apply quot_div_of_divide_pos__merge_transition; [lia |].
    match goal with HG : retval = Zgcd _ _ |- _ => rewrite HG end.
    apply Z.gcd_divide_r. }
  entailer_with ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_4 : extended_chinese_remainder_theorem_entail_wit_3_4.
Proof.
  crt_prepare.
  assert (Hnext : CRTPrefixMeaning residue_values modulus_values (i + 1)
    (answer + retval_2 * lcm)
    (lcm * (Znth i modulus_values 0 ÷ retval))).
  { eapply crt_prefix_meaning_merge__merge_transition with (gcd := retval);
      try eassumption; try lia.
    apply quot_div_of_divide_pos__merge_transition; [lia |].
    match goal with HG : retval = Zgcd _ _ |- _ => rewrite HG end.
    apply Z.gcd_divide_r. }
  entailer_with ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1.
Proof.
  crt_prepare.
  assert (Hresult : ExtendedCRTSystemResult residue_values modulus_values
    n_pre answer lcm).
  { eapply crt_prefix_meaning_to_result__prefix_boundaries with (i := i);
      [lia | lia | lia | eassumption]. }
  Exists lcm. entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i Hinputs ltac:(lia))
    as [[Hmpos Hmmax] [Hrpos Hrmax]].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_12 : extended_chinese_remainder_theorem_safety_wit_12.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i Hinputs ltac:(lia)) as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval ltac:(lia) PreH4 PreH3) as Hquotient.
  pose proof (proj1 PreH22) as Hlcm.
  pose proof (PreH14 i ltac:(lia)) as Hstep.
  rewrite <- Hlcm, <- PreH4 in Hstep.
  unfold ModularMul in PreH2. destruct PreH2 as [Hrange Hmul].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_13 : extended_chinese_remainder_theorem_safety_wit_13.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i Hinputs ltac:(lia)) as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval ltac:(lia) PreH4 PreH3) as Hquotient.
  pose proof (proj1 PreH23) as Hlcm.
  pose proof (PreH15 i ltac:(lia)) as Hstep.
  rewrite <- Hlcm, <- PreH4 in Hstep.
  unfold ModularMul in PreH2. destruct PreH2 as [Hrange Hmul].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_partial_solve_wit_8_pure : extended_chinese_remainder_theorem_partial_solve_wit_8_pure.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i Hinputs ltac:(lia))
    as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds
    lcm (Znth i modulus_values 0) retval ltac:(lia) PreH2 PreH1) as Hquotient.
  pose proof (signed_difference_division_bounds__machine_bounds
    (Znth i residue_values 0) answer retval ltac:(lia) ltac:(lia) PreH1)
    as Hdivision.
  match goal with
  | HP : CRTPrefixMeaning _ _ _ _ _,
    HS : forall k, 1 <= k < n_pre -> _ |- _ =>
    pose proof (proj1 HP) as Hlcm;
    pose proof (HS i ltac:(lia)) as Hstep;
    rewrite <- Hlcm, <- PreH2 in Hstep
  end.
  pose proof (bezout_coefficient_strict__gcd_branch_setup
    lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v
    Hmpos PreH2 PreH1 PreH5 PreH3 PreH4) as Hstrict.
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_partial_solve_wit_10_pure : extended_chinese_remainder_theorem_partial_solve_wit_10_pure.
Proof.
  crt_prepare.
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i Hinputs ltac:(lia))
    as [[Hmpos Hmmax] [Hrpos Hrmax]].
  pose proof (positive_gcd_quotient_bounds__machine_bounds
    lcm (Znth i modulus_values 0) retval ltac:(lia) PreH2 PreH1) as Hquotient.
  pose proof (signed_difference_division_bounds__machine_bounds
    (Znth i residue_values 0) answer retval ltac:(lia) ltac:(lia) PreH1)
    as Hdivision.
  match goal with
  | HP : CRTPrefixMeaning _ _ _ _ _,
    HS : forall k, 1 <= k < n_pre -> _ |- _ =>
    pose proof (proj1 HP) as Hlcm;
    pose proof (HS i ltac:(lia)) as Hstep;
    rewrite <- Hlcm, <- PreH2 in Hstep
  end.
  entailer_with ltac:(lia || int_auto).
Qed.
