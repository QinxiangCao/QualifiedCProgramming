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
From SimpleC.EE.LLM_bench.Algorithms.bucket_sort Require Import bucket_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib.
Local Open Scope sac.

From MaxMinLib Require Import MaxMin.
(** Array lengths are obtained from ownership, rather than duplicated in every
    invariant. All mathematical helpers below reuse the existing case library. *)
Ltac array_lengths :=
  repeat match goal with
  | |- ?P |-- _ =>
    match P with
    | context [IntArray.full ?a ?n ?l] =>
      match goal with
      | _ : Zlength l = n |- _ => fail 1
      | _ => prop_apply (IntArray.full_Zlength a n l); Intros
      end
    | context [IntArray.seg ?a ?lo ?hi ?l] =>
      match goal with
      | _ : Zlength l = hi - lo |- _ => fail 1
      | _ => prop_apply (IntArray.seg_Zlength a lo hi l); Intros
      end
    | context [IntArray.mixed_full ?a ?n ?l] =>
      match goal with
      | _ : Zlength l = n |- _ => fail 1
      | _ => prop_apply (IntArray.mixed_full_Zlength a n l); Intros
      end
    end
  end.

Ltac finish_state :=
  split_pure_spatial;
  [ repeat progress cancel; try reflexivity
  | split_pures; dump_pre_spatial; try assumption; try lia ].

Ltac value_bounds l k :=
  match goal with Hlo : Forall (Z.le 0) l |- _ =>
    let Hv := fresh "Hvalue_lower" in
    pose proof (proj1 (forall_znth__pass_transition (Z.le 0) 0 l)
      Hlo k ltac:(lia)) as Hv
  end;
  match goal with Hhi : Forall (Z.ge ?bound) l |- _ =>
    let Hv := fresh "Hvalue_upper" in
    pose proof (proj1 (forall_znth__pass_transition (Z.ge bound) 0 l)
      Hhi k ltac:(lia)) as Hv
  end.

Lemma proof_of_sort_safety_wit_17 : sort_safety_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  value_bounds counts digit.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_sort_safety_wit_21 : sort_safety_wit_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  value_bounds totals digit.
  value_bounds totals (digit - 1).
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_sort_entail_wit_1 : sort_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  value_bounds input 0.
  finish_state.
  unfold PrefixMaximum, max_value_of_subset, max_object_of_subset.
  sets_unfold.
  exists 0; split; [split | reflexivity]; try lia.
  intros k Hk; assert (k = 0) by lia; subst; lia.
Qed.

Lemma proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  value_bounds input i.
  finish_state.
  eapply prefix_maximum_extend_greater__maximum_pass_entry; eauto; lia.
Qed.

Lemma proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  finish_state.
  eapply prefix_maximum_extend_bounded__maximum_pass_entry; eauto.
Qed.

Lemma proof_of_sort_entail_wit_3 : sort_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia; subst i.
  Exists input.
  finish_state.
  - exists 0; cbn; lia.
  - split; [apply Permutation_refl |].
    intros left right Hbounds; rewrite !Z.mod_1_r; lia.
Qed.

Lemma proof_of_sort_entail_wit_4 : sort_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (exponent <= 100000000) by
    (eapply decimal_exponent_active_bound__maximum_pass_entry; eauto; lia).
  Exists (@nil Z) current_2.
  split_pure_spatial.
  - rewrite IntArray.seg_empty.
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("count")) 10).
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia; constructor.
Qed.

Lemma proof_of_sort_entail_wit_5 : sort_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (zero_prefix_2 ++ 0 :: nil) current_2.
  finish_state.
  apply Forall_app; split; [assumption | repeat constructor].
Qed.

Lemma proof_of_sort_entail_wit_6 : sort_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (digit = 10) by lia; subst digit.
  array_lengths.
  assert (Hcounts_lower : Forall (Z.le 0) zero_prefix).
  { eapply Forall_impl; [| exact PreH13]; intros x Hx; lia. }
  assert (Hcounts_upper : Forall (Z.ge 0) zero_prefix).
  { eapply Forall_impl; [| exact PreH13]; intros x Hx; lia. }
  assert (Hhist : DigitHistogramPrefix current_2 exponent 0 zero_prefix).
  { apply digit_histogram_prefix_zero__count_zero_init.
    intros k Hk.
    pose proof (proj1 (forall_znth__pass_transition (eq 0) 0 zero_prefix)
      PreH13 k ltac:(lia)); lia. }
  Exists zero_prefix current_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.seg_to_full (&("count")) 0 10 zero_prefix).
    replace ((&("count")) + 0 * sizeof (INT)) with (&("count")) by lia.
    replace (10 - 0) with 10 by lia.
    repeat progress cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_sort_entail_wit_7 : sort_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  value_bounds current i.
  pose proof (c_radix_digit_range__stable_placement
    (Znth i current 0) exponent ltac:(lia) ltac:(lia)).
  Exists counts_2 current.
  finish_state.
Qed.

Lemma proof_of_sort_entail_wit_8 : sort_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  repeat rewrite Zlength_replace_Znth in *.
  value_bounds current_2 i.
  value_bounds counts_2 digit.
  assert (Hdigit : digit = RadixDigit (Znth i current_2 0) exponent).
  { rewrite PreH18; symmetry; apply radix_digit_c_bridge__stable_placement; lia. }
  assert (Hhist : DigitHistogramPrefix current_2 exponent (i + 1)
    (replace_Znth digit (Znth digit counts_2 0 + 1) counts_2)).
  { rewrite Hdigit.
    apply digit_histogram_prefix_step__histogram_update; try assumption; lia. }
  Exists (replace_Znth digit (Znth digit counts_2 0 + 1) counts_2) current_2.
  finish_state.
  all: apply (proj2 (forall_znth__pass_transition _ 0 _));
    intros k Hk; rewrite Zlength_replace_Znth in Hk;
    destruct (Z.eq_dec k digit) as [-> | Hneq].
  all: try (rewrite Znth_replace_Znth_Same by lia; lia).
  all: rewrite Znth_replace_Znth_Diff by lia;
    value_bounds counts_2 k; lia.
Qed.

Lemma proof_of_sort_entail_wit_9 : sort_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia; subst i.
  array_lengths.
  Exists counts current_2 counts.
  finish_state.
  apply digit_prefix_totals_init__prefix_totals; assumption.
Qed.

Lemma proof_of_sort_entail_wit_10 : sort_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  repeat rewrite Zlength_replace_Znth in *.
  pose proof (digit_prefix_totals_step__prefix_totals histogram_2 totals_2 digit
    PreH4 ltac:(lia) ltac:(lia) PreH22) as Hprefix_step.
  pose proof (digit_histogram_prefix_mass_bound__prefix_totals
    current_2 exponent n_pre histogram_2 digit
    ltac:(lia) PreH4 PreH21 ltac:(lia)) as Hprefix_mass.
  assert (Hnew_value : 0 <= Znth digit totals_2 0 + Znth (digit - 1) totals_2 0 <= n_pre).
  { pose proof (proj1 (Hprefix_step digit ltac:(lia)) ltac:(lia)) as Hupdated.
    rewrite Znth_replace_Znth_Same in Hupdated by lia.
    rewrite <- Hupdated in Hprefix_mass; exact Hprefix_mass. }
  Exists (replace_Znth digit (Znth digit totals_2 0 + Znth (digit - 1) totals_2 0) totals_2)
    current_2 histogram_2.
  finish_state.
  all: apply (proj2 (forall_znth__pass_transition _ 0 _));
    intros k Hk; rewrite Zlength_replace_Znth in Hk;
    destruct (Z.eq_dec k digit) as [-> | Hneq].
  all: try (rewrite Znth_replace_Znth_Same by lia; lia).
  all: rewrite Znth_replace_Znth_Diff by lia;
    value_bounds totals_2 k; lia.
Qed.

Lemma proof_of_sort_entail_wit_11 : sort_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (digit = 10) by lia; subst digit.
  array_lengths.
  set (mixed := repeat (None : option Z) (Z.to_nat 1000)).
  assert (Hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2).
  { replace (Zlength current_2) with n_pre by lia; assumption. }
  assert (Hprogress : BucketPlacementProgress current_2 exponent n_pre histogram_2 totals mixed).
  { replace n_pre with (Zlength current_2) by lia.
    unfold mixed; apply bucket_placement_initial__stable_placement; assumption. }
  Exists mixed totals current_2 histogram_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_mixed_full (&("output")) 1000).
    unfold mixed; cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    replace ((n_pre - 1) + 1) with n_pre by lia; assumption.
Qed.

Lemma proof_of_sort_entail_wit_12 : sort_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  value_bounds current i.
  set (digit := Z.rem (Z.quot (Znth i current 0) exponent) 10).
  assert (Hdigit_range : 0 <= digit < 10).
  { unfold digit; apply c_radix_digit_range__stable_placement; lia. }
  assert (Hdigit : digit = RadixDigit (Znth i current 0) exponent).
  { unfold digit; symmetry; apply radix_digit_c_bridge__stable_placement; lia. }
  assert (Hpositive : 1 <= Znth digit counters_2 0).
  { rewrite Hdigit.
    eapply bucket_progress_counter_for_index__stable_placement
      with (remaining := i + 1) (histogram := histogram_2)
           (mixed_output := mixed_output_2); try eassumption; try lia.
    replace (Zlength current) with n_pre by lia; assumption. }
  value_bounds counters_2 digit.
  Exists mixed_output_2 counters_2 current histogram_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_split_to_missing_i
      (&("count")) digit 10 counters_2 0 ltac:(lia)).
    unfold digit; repeat progress cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_sort_entail_wit_13 : sort_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  repeat rewrite Zlength_replace_Znth in *.
  value_bounds current_2 i.
  assert (Hdigit : digit = RadixDigit (Znth i current_2 0) exponent).
  { rewrite PreH22; symmetry; apply radix_digit_c_bridge__stable_placement; lia. }
  assert (Hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2).
  { replace (Zlength current_2) with n_pre by lia; assumption. }
  set (next_counters := replace_Znth digit (Znth digit counters_2 0 - 1) counters_2).
  set (next_output := replace_Znth (Znth digit counters_2 0 - 1)
    (Some (Znth i current_2 0)) mixed_output_2).
  assert (Hprogress : BucketPlacementProgress current_2 exponent i histogram_2
    next_counters next_output).
  { pose proof (bucket_placement_step__stable_placement
      current_2 exponent histogram_2 counters_2 mixed_output_2 i
      PreH3 ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite <- Hdigit; lia) Hhist PreH21) as Hstep.
    cbv zeta in Hstep.
    rewrite <- Hdigit in Hstep.
    rewrite Znth_replace_Znth_Same in Hstep by lia.
    apply Hstep; lia. }
  Exists next_output next_counters current_2 histogram_2.
  unfold next_output, next_counters.
  finish_state.
  all: try (replace ((i - 1) + 1) with i by lia; exact Hprogress).
  all: apply (proj2 (forall_znth__pass_transition _ 0 _));
    intros k Hk; rewrite Zlength_replace_Znth in Hk;
    destruct (Z.eq_dec k digit) as [-> | Hneq].
  all: try (rewrite Znth_replace_Znth_Same by lia; lia).
  all: rewrite Znth_replace_Znth_Diff by lia;
    value_bounds counters_2 k; lia.
Qed.

Lemma proof_of_sort_entail_wit_14 : sort_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  assert (Hi : i = -1) by lia.
  assert (Hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram).
  { replace (Zlength current_2) with n_pre by lia; assumption. }
  assert (Hdigits : forall k, 0 <= k < Zlength current_2 ->
    0 <= RadixDigit (Znth k current_2 0) exponent < 10).
  { intros k Hk; value_bounds current_2 k.
    rewrite radix_digit_c_bridge__stable_placement by lia.
    apply c_radix_digit_range__stable_placement; lia. }
  assert (Hprogress : BucketPlacementProgress current_2 exponent 0 histogram counters mixed_output).
  { replace 0 with (i + 1) by lia; assumption. }
  pose proof (bucket_placement_complete__stable_placement current_2 exponent
    histogram counters mixed_output PreH4 ltac:(lia) ltac:(lia)
    Hhist Hdigits Hprogress) as [Hstarts Hmixed_prefix].
  set (pass_output := RadixStableOutput current_2 exponent).
  pose proof (radix_stable_output_permutation__stable_placement
    current_2 exponent Hdigits) as Hperm.
  assert (Hpass_len : Zlength pass_output = n_pre).
  { unfold pass_output; pose proof (Permutation_length Hperm) as Hlen.
    rewrite !Zlength_correct in *; lia. }
  assert (Hpass_lower : Forall (Z.le 0) pass_output).
  { eapply Permutation_Forall; [exact Hperm | exact PreH12]. }
  assert (Hpass_upper : Forall (Z.ge 999999999) pass_output).
  { eapply Permutation_Forall; [exact Hperm | exact PreH13]. }
  assert (Hstable : StableDigitPass current_2 pass_output exponent) by reflexivity.
  assert (Hcopy : RadixCopyPrefix current_2 pass_output current_2 0)
    by apply radix_copy_prefix_zero__copy_back.
  assert (Hmixed_prefix_n : sublist 0 n_pre mixed_output = map (@Some Z) pass_output).
  { replace n_pre with (Zlength current_2) by lia; exact Hmixed_prefix. }
  Exists counters current_2 pass_output current_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.mixed_full_split_to_mixed_seg
      (&("output")) n_pre 1000 mixed_output).
    + dump_pre_spatial; lia.
    + rewrite Hmixed_prefix_n.
      sep_apply_l_atomic (IntArray.mixed_seg_to_seg (&("output")) 0 n_pre pass_output).
      sep_apply_l_atomic (IntArray.mixed_seg_to_undef_seg (&("output")) n_pre 1000
        (sublist n_pre 1000 mixed_output)).
      repeat progress cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_sort_entail_wit_15 : sort_entail_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  repeat rewrite Zlength_replace_Znth in *.
  replace (i - 0) with i by lia.
  Exists bucket_starts_2 (replace_Znth i (Znth i pass_output_2 0) working_2)
    pass_output_2 current_2.
  finish_state.
  apply radix_copy_prefix_step__copy_back; try assumption; lia.
Qed.

Lemma proof_of_sort_entail_wit_16 : sort_entail_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  assert (Hi : i = n_pre) by lia.
  assert (Hworking : working = pass_output).
  { apply (proj2 (list_eq_ext working pass_output 0)); split; [lia |].
    intros k Hk; apply (proj1 PreH17); lia. }
  subst working.
  assert (Hnext_exponent : DecimalExponent (exponent * 10)).
  { apply decimal_exponent_next__pass_transition; assumption. }
  assert (Hnext_state : RadixPassState input pass_output (exponent * 10)).
  { destruct PreH15 as [Hperm Hordered]; split.
    - eapply Permutation_trans; [exact Hperm |].
      apply stable_digit_pass_permutation__pass_transition with (exponent := exponent); assumption.
    - eapply stable_digit_pass_next_order__pass_transition; eauto; lia. }
  Exists pass_output.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_undef_seg (&("output")) 0 n_pre pass_output).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("output")) 0 n_pre 1000 ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&("count")) 10 bucket_starts).
    simpl.
    replace ((&("output")) + 0) with (&("output")) by lia.
    repeat progress cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_sort_return_wit_1 : sort_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  Exists input.
  finish_state.
  - apply Permutation_refl.
  - apply increasing_short_list__final_result; lia.
Qed.

Lemma proof_of_sort_return_wit_2 : sort_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  array_lengths.
  assert (Hperm : Permutation input current) by exact (proj1 PreH12).
  assert (Hinput_length : Zlength input = n_pre).
  { pose proof (Permutation_length Hperm) as Hlen; rewrite !Zlength_correct in *; lia. }
  assert (Hsorted : increasing current).
  { eapply radix_pass_state_final_increasing__final_result
      with (input := input) (n := n_pre) (exponent := exponent) (maximum := max_value);
      try assumption; try lia.
    intros k Hk; value_bounds current k; lia. }
  Exists current; finish_state.
Qed.
