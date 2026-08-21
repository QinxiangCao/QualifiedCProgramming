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
From SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp Require Import concatenating_numbers_dp_goal.
From SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp Require Import concatenating_numbers_dp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_lib.
Local Open Scope sac.

Lemma proof_of_compare_concatenated_order_safety_wit_1_split_goal_1 : compare_concatenated_order_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_safety_wit_1_split_goal_2 : compare_concatenated_order_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_safety_wit_1 : compare_concatenated_order_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_compare_concatenated_order_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_compare_concatenated_order_safety_wit_1_split_goal_2.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 : compare_concatenated_order_entail_wit_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_1.
  intros.
  unfold ConcatCompareLoopState.
  split; [reflexivity |].
  split; [reflexivity |].
  apply ConcatComparePrefix_zero__compare_bounds.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 : compare_concatenated_order_entail_wit_1_split_goal_2.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_2.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_3 : compare_concatenated_order_entail_wit_1_split_goal_3.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_3.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 : compare_concatenated_order_entail_wit_1_split_goal_4.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_4.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 : compare_concatenated_order_entail_wit_1_split_goal_5.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_5.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  specialize (Hentries right_pre ltac:(lia)).
  destruct Hentries as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 : compare_concatenated_order_entail_wit_1_split_goal_6.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_6.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  specialize (Hentries right_pre ltac:(lia)).
  destruct Hentries as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_7 : compare_concatenated_order_entail_wit_1_split_goal_7.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_7.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  specialize (Hentries left_pre ltac:(lia)).
  destruct Hentries as [_ [Hleft_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_8 : compare_concatenated_order_entail_wit_1_split_goal_8.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_8.
  intros.
  unfold RowsWellFormed in PreH9.
  destruct PreH9 as [_ [_ Hentries]].
  specialize (Hentries left_pre ltac:(lia)).
  destruct Hentries as [_ [Hleft_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1 : compare_concatenated_order_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_1.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_2.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_3.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_4.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_5.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_6.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_7.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_1_split_goal_8.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 : compare_concatenated_order_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hleft_count : left_pre < count) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hleft_mul :
    left_pre * number_width_pre <=
    (count - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count * number_width_pre) with
    ((count - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_3 : compare_concatenated_order_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_3_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 : compare_concatenated_order_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hright_count : right_pre < count) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hpos_tail : position - left_length < number_width_pre) by lia.
  assert (Hright_mul :
    right_pre * number_width_pre <=
    (count - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count * number_width_pre) with
    ((count - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_5 : compare_concatenated_order_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_5_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_6_1_split_goal_1 : compare_concatenated_order_entail_wit_6_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_6_1_split_goal_1.
  intros.
  unfold ConcatCompareLoopState in PreH36.
  destruct PreH36 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position PreH34 PreH35 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [Hleft_direct [_ [_ _]]].
  apply Hleft_direct; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_6_1 : compare_concatenated_order_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_6_1_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_6_2_split_goal_1 : compare_concatenated_order_entail_wit_6_2_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_6_2_split_goal_1.
  intros.
  unfold ConcatCompareLoopState in PreH34.
  destruct PreH34 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position PreH32 PreH33 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [_ [Hleft_offset [_ _]]].
  apply Hleft_offset; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_6_2 : compare_concatenated_order_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_6_2_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 : compare_concatenated_order_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hright_count : right_pre < count) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hright_mul :
    right_pre * number_width_pre <=
    (count - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count * number_width_pre) with
    ((count - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_8 : compare_concatenated_order_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_8_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_10_split_goal_1 : compare_concatenated_order_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hleft_count : left_pre < count) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hpos_tail : position - right_length < number_width_pre) by lia.
  assert (Hleft_mul :
    left_pre * number_width_pre <=
    (count - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count * number_width_pre) with
    ((count - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_10 : compare_concatenated_order_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_10_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_11_1_split_goal_1 : compare_concatenated_order_entail_wit_11_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_11_1_split_goal_1.
  intros.
  unfold ConcatCompareLoopState in PreH36.
  destruct PreH36 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position PreH34 PreH35 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [_ [_ [Hright_direct _]]].
  apply Hright_direct; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_11_1 : compare_concatenated_order_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_11_1_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_11_2_split_goal_1 : compare_concatenated_order_entail_wit_11_2_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_11_2_split_goal_1.
  intros.
  unfold ConcatCompareLoopState in PreH34.
  destruct PreH34 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position PreH32 PreH33 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [_ [_ [_ Hright_offset]]].
  apply Hright_offset; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_11_2 : compare_concatenated_order_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_11_2_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_12_split_goal_1 : compare_concatenated_order_entail_wit_12_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_12_split_goal_1.
  intros.
  eapply concat_compare_prefix_step__compare_semantics; eauto; try lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_12 : compare_concatenated_order_entail_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_12_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_return_wit_1_split_goal_1 : compare_concatenated_order_return_wit_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_return_wit_1_split_goal_1.
  intros.
  eapply concat_compare_outcome_at_end__compare_semantics; eauto; lia.
Qed.

Lemma proof_of_compare_concatenated_order_return_wit_1 : compare_concatenated_order_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_return_wit_2_split_goal_1 : compare_concatenated_order_return_wit_2_split_goal_1.
Proof.
  unfold compare_concatenated_order_return_wit_2_split_goal_1.
  intros.
  eapply concat_compare_outcome_at_difference__compare_semantics; eauto;
    try lia.
Qed.

Lemma proof_of_compare_concatenated_order_return_wit_2 : compare_concatenated_order_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_compare_concatenated_order_return_wit_3_split_goal_1 : compare_concatenated_order_return_wit_3_split_goal_1.
Proof.
  unfold compare_concatenated_order_return_wit_3_split_goal_1.
  intros.
  eapply concat_compare_outcome_at_difference__compare_semantics; eauto;
    try lia.
Qed.

Lemma proof_of_compare_concatenated_order_return_wit_3 : compare_concatenated_order_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_1 : concatenating_numbers_dp_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  replace (1 * 2 ^ count_pre) with (Z.shiftl 1 count_pre).
  2: { rewrite Z.shiftl_mul_pow2 by lia; ring. }
  rewrite signed_last_nbits_eq by lia.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_2 : concatenating_numbers_dp_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  replace (1 * 2 ^ count_pre) with (Z.shiftl 1 count_pre).
  2: { rewrite Z.shiftl_mul_pow2 by lia; ring. }
  rewrite signed_last_nbits_eq by lia.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_3 : concatenating_numbers_dp_safety_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_4 : concatenating_numbers_dp_safety_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_1 : concatenating_numbers_dp_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_2.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_3.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_4.
Qed. 

Lemma proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_1 : concatenating_numbers_dp_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  change (bit_value * 2 <= 2147483647).
  pose proof (signed_last_nbits_double_power__bit_scan
    bit_value state_count count_pre ltac:(lia) ltac:(lia) ltac:(eauto)
    ltac:(lia)) as Hrange.
  change (-2147483648 <= bit_value * 2 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_2 : concatenating_numbers_dp_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  change (-2147483648 <= bit_value * 2).
  pose proof (signed_last_nbits_double_power__bit_scan
    bit_value state_count count_pre ltac:(lia) ltac:(lia) ltac:(eauto)
    ltac:(lia)) as Hrange.
  change (-2147483648 <= bit_value * 2 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_3 : concatenating_numbers_dp_safety_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_4 : concatenating_numbers_dp_safety_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_11 : concatenating_numbers_dp_safety_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_2.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_3.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_4.
Qed. 

Lemma proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_1 : concatenating_numbers_dp_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ first) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ first) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2 : concatenating_numbers_dp_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ first) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ first) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_3 : concatenating_numbers_dp_safety_wit_28_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_4 : concatenating_numbers_dp_safety_wit_28_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_28 : concatenating_numbers_dp_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_3.
  - Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_4.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_1 : concatenating_numbers_dp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hshift :
    signed_last_nbits (Z.shiftl 1 count_pre) 32 = Z.shiftl 1 count_pre).
  {
    rewrite signed_last_nbits_eq by lia.
    reflexivity.
  }
  rewrite Hshift.
  Exists (-1 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single best_first_pre 0 (-1)).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
    cancel (IntArray.full lengths_pre count_pre lens).
    cancel (IntArray.seg best_first_pre 0 1 (-1 :: nil)).
    cancel (IntArray.undef_seg best_first_pre 1 (Z.shiftl 1 count_pre)).
    cancel (IntArray.undef_full result_pre (sum lens)).
  - split_pures.
    all: try (dump_pre_spatial; auto; try lia).
    apply dp_table_prefix_singleton__dp_initialization.
    lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 : concatenating_numbers_dp_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold BitScanState.
  rewrite Z.shiftl_1_l in PreH2 |- *.
  simpl.
  repeat split; try lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_2 : concatenating_numbers_dp_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1 : concatenating_numbers_dp_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  unfold BitScanState in PreH19.
  destruct PreH19 as (Hmaskrange & Hbitbounds & Hvalue & Hlower_old).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  unfold BitScanState.
  split; [exact Hmaskrange |].
  split; [lia |].
  split.
  - change (bit_value * 2 = Z.shiftl 1 (bit + 1)).
    exact Hdouble.
  - exact Hlower_next.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 : concatenating_numbers_dp_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  change (bit_value * 2 <= state_count).
  rewrite PreH2.
  exact Hupper.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 : concatenating_numbers_dp_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  change (1 <= bit_value * 2).
  exact Hpositive.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4 : concatenating_numbers_dp_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3 : concatenating_numbers_dp_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 : concatenating_numbers_dp_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  unfold SelectedBitState.
  split; [exact PreH19 |].
  split; [exact PreH1 |].
  split; [lia |].
  split; [exact Hmaskbit |].
  split; [reflexivity |].
  exact Hxor.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 : concatenating_numbers_dp_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 : concatenating_numbers_dp_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 : concatenating_numbers_dp_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  rewrite PreH2.
  exact Hvalue_small.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 : concatenating_numbers_dp_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value PreH19 PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  exact Hbitlt.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4 : concatenating_numbers_dp_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_5 : concatenating_numbers_dp_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH19 as Hprefix.
  unfold DPTablePrefix in Hprefix.
  destruct Hprefix as [Hcomputed [Hlength [Hzero Hall]]].
  destruct (Z.eq_dec rest 0) as [Hrest_zero | Hrest_nonzero].
  - Left.
    Exists choices.
    split_pure_spatial.
    + cancel (IntArray.seg best_first_pre 0 mask choices).
      cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
      cancel (IntArray.full lengths_pre count_pre lens).
      cancel (IntArray.undef_seg best_first_pre mask state_count).
      cancel (IntArray.undef_full result_pre (sum lens)).
    + split_pures; dump_pre_spatial; auto; try lia.
      * replace (rest - 0) with rest by lia. reflexivity.
      * subst rest. exact Hzero.
  - assert (Hrest_positive : 1 <= rest) by lia.
    assert (Hbest :
      BestIndexForMask rows lens count_pre rest (Znth rest choices 0)).
    { apply Hall. lia. }
    pose proof Hbest as [Hbest_bounds [Hrest_selected Hbest_other]].
    replace (rest - 0) with rest by lia.
    Right.
    Exists choices.
    split_pure_spatial.
    + cancel (IntArray.seg best_first_pre 0 mask choices).
      cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
      cancel (IntArray.full lengths_pre count_pre lens).
      cancel (IntArray.undef_seg best_first_pre mask state_count).
      cancel (IntArray.undef_full result_pre (sum lens)).
    + split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 : concatenating_numbers_dp_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply
    (dp_table_prefix_extend__dp_table_transition
       rows lens count_pre mask choices_2 bit).
  - exact PreH21.
  - lia.
  - eapply
      (best_index_singleton__dp_table_transition
         rows lens count_pre mask bit bit_value rest);
      [exact PreH22 | exact PreH17].
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 : concatenating_numbers_dp_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_1 : concatenating_numbers_dp_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 : concatenating_numbers_dp_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply dp_table_prefix_extend__dp_table_transition; eauto.
  - lia.
  - eapply best_index_choose_bit__dp_table_transition; eauto.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 : concatenating_numbers_dp_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_2 : concatenating_numbers_dp_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 : concatenating_numbers_dp_entail_wit_6_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply dp_table_prefix_extend__dp_table_transition; eauto.
  - lia.
  - eapply best_index_keep_previous__dp_table_transition; eauto.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 : concatenating_numbers_dp_entail_wit_6_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_3 : concatenating_numbers_dp_entail_wit_6_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_8 : concatenating_numbers_dp_entail_wit_8.
Proof.
  aggressive_pre_process.
  assert (Hmask : mask = state_count) by lia.
  subst mask.
  Exists choices_2.
  split_pure_spatial.
  - replace (Zlength choices_2) with state_count by lia.
    sep_apply (IntArray.seg_to_full best_first_pre 0 state_count choices_2).
    replace (best_first_pre + 0 * sizeof(INT)) with best_first_pre by lia.
    replace (state_count - 0) with state_count by lia.
    cancel.
  - split_pures; dump_pre_spatial; try rewrite Zlength_nil; try lia; try assumption.
    + replace state_count with (Zlength choices_2) by lia.
      exact PreH14.
    + rewrite PreH2.
      apply greedy_output_full_mask__output_initialization.
      * unfold RowsWellFormed in PreH11. tauto.
      * lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_1 : concatenating_numbers_dp_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  unfold DPTablePrefix in PreH17.
  destruct PreH17 as [_ [_ [_ Htable]]].
  apply Htable. lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_2 : concatenating_numbers_dp_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hbest : BestIndexForMask rows lens count_pre mask
    (Znth mask choices 0)).
  { unfold DPTablePrefix in PreH17.
    destruct PreH17 as [_ [_ [_ Htable]]].
    apply Htable. lia. }
  destruct Hbest as [Hindex [Hbit Hgreatest]].
  rewrite PreH11.
  eapply greedy_output_remaining_length__output_initialization; eauto.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_3 : concatenating_numbers_dp_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  unfold DPTablePrefix in PreH17.
  destruct PreH17 as [_ [_ [_ Htable]]].
  specialize (Htable mask ltac:(lia)).
  destruct Htable as [Hindex _].
  unfold RowsWellFormed in PreH14.
  destruct PreH14 as [_ [_ Hrows]].
  specialize (Hrows (Znth mask choices 0) Hindex).
  tauto.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_4 : concatenating_numbers_dp_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
  unfold DPTablePrefix in PreH17.
  destruct PreH17 as [_ [_ [_ Htable]]].
  specialize (Htable mask ltac:(lia)).
  destruct Htable as [Hindex _].
  unfold RowsWellFormed in PreH14.
  destruct PreH14 as [_ [_ Hrows]].
  specialize (Hrows (Znth mask choices 0) Hindex).
  tauto.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_5 : concatenating_numbers_dp_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(auto).
  unfold DPTablePrefix in PreH17.
  destruct PreH17 as [_ [_ [_ Htable]]].
  specialize (Htable mask ltac:(lia)).
  unfold BestIndexForMask in Htable. lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_6 : concatenating_numbers_dp_entail_wit_9_split_goal_6.
Proof.
  LLM_pre_process ltac:(auto).
  unfold DPTablePrefix in PreH17.
  destruct PreH17 as [_ [_ [_ Htable]]].
  specialize (Htable mask ltac:(lia)).
  unfold BestIndexForMask in Htable. lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_9 : concatenating_numbers_dp_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_4.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_5.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_6.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_10 : concatenating_numbers_dp_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists output_2 output_2 choices_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
    cancel (IntArray.full lengths_pre count_pre lens).
    cancel (IntArray.full best_first_pre state_count choices_2).
    cancel (IntArray.seg result_pre 0 result_length output_2).
    cancel (IntArray.undef_seg result_pre result_length (sum lens)).
  - split_pures; dump_pre_spatial; auto; try lia.
    unfold AppendRowPrefix.
    change (sublist 0 0 (item_digits (item_at rows lens first))) with (@nil Z).
    rewrite app_nil_r.
    reflexivity.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_11_split_goal_1 : concatenating_numbers_dp_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hfirst_count : first < count_pre) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hfirst_mul :
    first * number_width_pre <=
    (count_pre - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count_pre * number_width_pre) with
    ((count_pre - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_11 : concatenating_numbers_dp_entail_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_11_split_goal_1.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_13 : concatenating_numbers_dp_entail_wit_13.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hposition_next : 0 <= position + 1) by lia.
  assert (Hprefix_next :
    AppendRowPrefix rows lens prior_2 first (position + 1)
      (output_2 +:: Znth (first * number_width_pre + position) flat 0)).
  { eapply append_row_prefix_step__output_row_copy; eauto. }
  assert (Houtput_length :
    result_length + 1 =
    Zlength (output_2 +::
      Znth (first * number_width_pre + position) flat 0)).
  { rewrite Zlength_app_cons. lia. }
  assert (Hremaining :
    result_length + 1 +
      (Znth first lens 0 - (position + 1)) <= sum lens) by lia.
  Exists prior_2
    (output_2 +:: Znth (first * number_width_pre + position) flat 0)
    choices_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
    cancel (IntArray.full lengths_pre count_pre lens).
    cancel (IntArray.full best_first_pre state_count choices_2).
    cancel (IntArray.seg result_pre 0 (result_length + 1)
      (output_2 +:: Znth (first * number_width_pre + position) flat 0)).
    cancel (IntArray.undef_seg result_pre (result_length + 1) (sum lens)).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_1 : concatenating_numbers_dp_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hshift :
      signed_last_nbits (Z.shiftl 1 first) 32 = Z.shiftl 1 first).
  { apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    split.
    - assert (0 < 2 ^ first) by (apply Z.pow_pos_nonneg; lia).
      lia.
    - apply Z.pow_lt_mono_r; lia. }
  rewrite Hshift.
  eapply greedy_output_consume_best__output_finalization; eauto.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_2 : concatenating_numbers_dp_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hshift :
      signed_last_nbits (Z.shiftl 1 first) 32 = Z.shiftl 1 first).
  { apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    split.
    - assert (0 < 2 ^ first) by (apply Z.pow_pos_nonneg; lia).
      lia.
    - apply Z.pow_lt_mono_r; lia. }
  rewrite Hshift.
  rewrite Z.shiftl_mul_pow2 in PreH2 by lia.
  rewrite Z.mul_1_l in PreH2.
  assert (Hbitbounds : 0 <= Z.shiftl 1 first < 2 ^ count_pre).
  { rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    split.
    - apply Z.pow_nonneg; lia.
    - apply Z.pow_lt_mono_r; lia. }
  pose proof
    (lxor_lt_pow2__output_finalization
       mask (Z.shiftl 1 first) count_pre ltac:(lia) Hbitbounds ltac:(lia))
    as Hxor.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_3 : concatenating_numbers_dp_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hshift :
      signed_last_nbits (Z.shiftl 1 first) 32 = Z.shiftl 1 first).
  { apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    split.
    - assert (0 < 2 ^ first) by (apply Z.pow_pos_nonneg; lia).
      lia.
    - apply Z.pow_lt_mono_r; lia. }
  rewrite Hshift.
  rewrite Z.shiftl_mul_pow2 in PreH2 by lia.
  rewrite Z.mul_1_l in PreH2.
  assert (Hbitbounds : 0 <= Z.shiftl 1 first < 2 ^ count_pre).
  { rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    split.
    - apply Z.pow_nonneg; lia.
    - apply Z.pow_lt_mono_r; lia. }
  pose proof
    (lxor_lt_pow2__output_finalization
       mask (Z.shiftl 1 first) count_pre ltac:(lia) Hbitbounds ltac:(lia))
    as Hxor.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_14 : concatenating_numbers_dp_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_3.
Qed. 

Lemma proof_of_concatenating_numbers_dp_return_wit_1 : concatenating_numbers_dp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  - assert (Hgreedy_zero :
        GreedyOutputPrefix rows lens count_pre 0 output_2).
    { rewrite <- PreH1; exact PreH18. }
    pose proof
      (greedy_output_empty_mask__output_finalization
         rows lens count_pre number_width_pre output_2 PreH14 Hgreedy_zero)
      as [Hlargest Houtput_length].
    assert (Hresult_full : result_length = sum lens) by lia.
    Exists output_2 choices_2.
    split_pure_spatial.
    + rewrite Hresult_full.
      rewrite IntArray.undef_seg_empty.
      sep_apply (IntArray.seg_to_full result_pre 0 (sum lens) output_2).
      replace (result_pre + 0 * sizeof(INT)) with result_pre by lia.
      replace (sum lens - 0) with (sum lens) by lia.
      rewrite <- PreH2.
      cancel.
    + split_pures.
      * dump_pre_spatial; reflexivity.
      * dump_pre_spatial; rewrite <- PreH2; exact PreH17.
      * dump_pre_spatial; exact Hlargest.
      * dump_pre_spatial; exact Houtput_length.
Qed. 
