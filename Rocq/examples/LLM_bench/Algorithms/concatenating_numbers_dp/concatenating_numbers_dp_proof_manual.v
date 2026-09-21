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
Local Opaque IntArray.undef_full IntArray.undef_seg IntArray.full IntArray.seg.

(* The generated premises are explicit.  Reconstruct input facts only when
   an existing mathematical helper needs them. *)
Ltac annotation_wf :=
  eapply rows_explicit_facts__annotation; eassumption.

Ltac annotation_prepare :=
  try match goal with
  | Hr : Zlength ?rows = ?count,
    Hl : Zlength ?lens = ?count,
    Hw : Forall (eq ?width) (map (@Zlength Z) ?rows) |- _ =>
      let Hwf := fresh "Hinput" in
      assert (Hwf : (Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = width /\
       1 <= Znth i lens 0 <= width /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9)) by annotation_wf
  end.

Ltac annotation_fact := first [assumption | annotation_wf | lia | nia].



Ltac scratch_cancel :=
  sepcon_right_assoc;
  repeat match goal with
  | |- ?P ** _ |-- _ => progress (cancel P)
  | |- ?P |-- ?P => apply derivable1_refl
  end; try cancel.

Lemma proof_of_compare_concatenated_order_safety_wit_1_split_goal_1 : compare_concatenated_order_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  dump_pre_spatial.
  destruct old_PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_safety_wit_1_split_goal_2 : compare_concatenated_order_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  dump_pre_spatial.
  destruct old_PreH9 as [_ [_ Hentries]].
  pose proof (Hentries left_pre ltac:(lia)) as Hleft.
  pose proof (Hentries right_pre ltac:(lia)) as Hright.
  destruct Hleft as [_ [Hleft_length _]].
  destruct Hright as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_safety_wit_1 : compare_concatenated_order_safety_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_safety_wit_1_split_goal_1.
  Goal_apply proof_of_compare_concatenated_order_safety_wit_1_split_goal_2.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 : compare_concatenated_order_entail_wit_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_1.
  intros.
  all: annotation_prepare.

  unfold ConcatCompareLoopState.
  split; [reflexivity |].
  split; [reflexivity |].
  apply ConcatComparePrefix_zero__compare_bounds.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 : compare_concatenated_order_entail_wit_1_split_goal_2.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_2.
  intros.
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  destruct old_PreH9 as [_ [_ Hentries]].
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
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  destruct old_PreH9 as [_ [_ Hentries]].
  specialize (Hentries right_pre ltac:(lia)).
  destruct Hentries as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 : compare_concatenated_order_entail_wit_1_split_goal_4.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_4.
  intros.
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  destruct old_PreH9 as [_ [_ Hentries]].
  specialize (Hentries right_pre ltac:(lia)).
  destruct Hentries as [_ [Hright_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 : compare_concatenated_order_entail_wit_1_split_goal_5.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_5.
  intros.
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  destruct old_PreH9 as [_ [_ Hentries]].
  specialize (Hentries left_pre ltac:(lia)).
  destruct Hentries as [_ [Hleft_length _]].
  lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 : compare_concatenated_order_entail_wit_1_split_goal_6.
Proof.
  unfold compare_concatenated_order_entail_wit_1_split_goal_6.
  intros.
  all: annotation_prepare.
  assert (old_PreH9 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.

  destruct old_PreH9 as [_ [_ Hentries]].
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

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_2_split_goal_1 : compare_concatenated_order_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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

Lemma proof_of_compare_concatenated_order_entail_wit_2 : compare_concatenated_order_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_2_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 : compare_concatenated_order_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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

Lemma proof_of_compare_concatenated_order_entail_wit_3 : compare_concatenated_order_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_3_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_4_1_split_goal_1 : compare_concatenated_order_entail_wit_4_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_4_1_split_goal_1.
  intros.
  all: annotation_prepare.
  assert (old_PreH34 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.
  assert (old_PreH35 : (FlatRows flat rows count number_width_pre )) by annotation_fact.
  assert (old_PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) by annotation_fact.

  unfold ConcatCompareLoopState in old_PreH36.
  destruct old_PreH36 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position old_PreH34 old_PreH35 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [Hleft_direct [_ [_ _]]].
  apply Hleft_direct; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_4_1 : compare_concatenated_order_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_4_1_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_4_2_split_goal_1 : compare_concatenated_order_entail_wit_4_2_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_4_2_split_goal_1.
  intros.
  all: annotation_prepare.
  assert (old_PreH32 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.
  assert (old_PreH33 : (FlatRows flat rows count number_width_pre )) by annotation_fact.
  assert (old_PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) by annotation_fact.

  unfold ConcatCompareLoopState in old_PreH34.
  destruct old_PreH34 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position old_PreH32 old_PreH33 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [_ [Hleft_offset [_ _]]].
  apply Hleft_offset; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_4_2 : compare_concatenated_order_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_4_2_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 : compare_concatenated_order_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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

Lemma proof_of_compare_concatenated_order_entail_wit_5 : compare_concatenated_order_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_5_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_6_split_goal_1 : compare_concatenated_order_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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

Lemma proof_of_compare_concatenated_order_entail_wit_6 : compare_concatenated_order_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_6_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_7_1_split_goal_1 : compare_concatenated_order_entail_wit_7_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_7_1_split_goal_1.
  intros.
  all: annotation_prepare.
  assert (old_PreH34 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.
  assert (old_PreH35 : (FlatRows flat rows count number_width_pre )) by annotation_fact.
  assert (old_PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) by annotation_fact.

  unfold ConcatCompareLoopState in old_PreH36.
  destruct old_PreH36 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position old_PreH34 old_PreH35 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [_ [_ [Hright_direct _]]].
  apply Hright_direct; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_7_1 : compare_concatenated_order_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_7_1_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_7_2_split_goal_1 : compare_concatenated_order_entail_wit_7_2_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_7_2_split_goal_1.
  intros.
  all: annotation_prepare.
  assert (old_PreH32 : ((Zlength rows = count /\ Zlength lens = count /\
     forall i, 0 <= i < count ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.
  assert (old_PreH33 : (FlatRows flat rows count number_width_pre )) by annotation_fact.
  assert (old_PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) by annotation_fact.

  unfold ConcatCompareLoopState in old_PreH34.
  destruct old_PreH34 as [Hleft_length [Hright_length _]].
  pose proof (concat_digit_lookup__compare_digits
    flat rows lens count number_width_pre left_pre right_pre left_length
    right_length position old_PreH32 old_PreH33 ltac:(lia) ltac:(lia)
    Hleft_length Hright_length) as Hdigits.
  destruct Hdigits as
    [_ [_ [_ Hright_offset]]].
  apply Hright_offset; lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_7_2 : compare_concatenated_order_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_7_2_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 : compare_concatenated_order_entail_wit_8_split_goal_1.
Proof.
  unfold compare_concatenated_order_entail_wit_8_split_goal_1.
  intros.
  all: annotation_prepare.

  eapply concat_compare_prefix_step__compare_semantics; eauto; try lia.
Qed.

Lemma proof_of_compare_concatenated_order_entail_wit_8 : compare_concatenated_order_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_entail_wit_8_split_goal_1.

Qed. 

Lemma proof_of_compare_concatenated_order_return_wit_1_split_goal_1 : compare_concatenated_order_return_wit_1_split_goal_1.
Proof.
  unfold compare_concatenated_order_return_wit_1_split_goal_1.
  intros.
  all: annotation_prepare.

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
  all: annotation_prepare.

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
  all: annotation_prepare.

  eapply concat_compare_outcome_at_difference__compare_semantics; eauto;
    try lia.
Qed.

Lemma proof_of_compare_concatenated_order_return_wit_3 : compare_concatenated_order_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_compare_concatenated_order_return_wit_3_split_goal_1.

Qed. 

Lemma proof_of_concatenating_numbers_dp_safety_wit_1 : concatenating_numbers_dp_safety_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (signed_Lastnbits_range (1 * 2 ^ count_pre) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (1 * 2 ^ count_pre) 32 < 2147483648) in Hrange.
  entailer_with ltac:(lia || int_auto).
Qed. 

Lemma proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_1 : concatenating_numbers_dp_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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
  all: annotation_prepare.

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
  all: annotation_prepare.

  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ first) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ first) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2 : concatenating_numbers_dp_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_3.
  Goal_apply proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_4.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_1 : concatenating_numbers_dp_entail_wit_1.
Proof.
  unfold concatenating_numbers_dp_entail_wit_1. left. intros.
  assert (Hwidth : Forall (fun row : list Z => Zlength row = number_width_pre) rows).
  { apply decimal_rows_lengths_from_map. assumption. }
  subst flat.
  assert (Hflat : FlatRows (concat rows) rows count_pre number_width_pre).
  { unfold FlatRows. split.
    - rewrite decimal_rows_flat_length with (width := number_width_pre) by exact Hwidth. lia.
    - split; [assumption |]. intros k Hk.
      apply decimal_rows_flat_row; try assumption; lia. }
  assert (Hshift : signed_last_nbits (Z.shiftl 1 count_pre) 32 = Z.shiftl 1 count_pre).
  { rewrite signed_last_nbits_eq by lia. reflexivity. }
  rewrite Hshift.
  sep_apply (IntArray.undef_seg_split_to_undef_seg (&("best_first")) 1 (Z.shiftl 1 count_pre) 1048576 ltac:(lia)).
  sep_apply (decimal_rows_flatten rows numbers_pre count_pre number_width_pre ltac:(lia) ltac:(lia)).
  sep_apply (IntArray.seg_single (&("best_first")) 0 (-1)).
  replace (0 + 1) with 1 by lia.
  Exists (-1 :: nil).
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try reflexivity.
    apply dp_table_prefix_singleton__dp_initialization. lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 : concatenating_numbers_dp_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.

  unfold BitScanState.
  rewrite Z.shiftl_1_l in old_PreH2 |- *.
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
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) = 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  unfold BitScanState in old_PreH19.
  destruct old_PreH19 as (Hvalue & Hlower_old).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  unfold BitScanState.
  split.
  - change (bit_value * 2 = Z.shiftl 1 (bit + 1)).
    exact Hdouble.
  - exact Hlower_next.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 : concatenating_numbers_dp_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) = 0)) by annotation_fact.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq.
  2: lia.
  2: { eapply (signed_last_nbits_double_power__bit_scan
         bit_value state_count count_pre); eauto. }
  change (bit_value * 2 <= state_count).
  rewrite old_PreH2.
  exact Hupper.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 : concatenating_numbers_dp_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) = 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
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
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) = 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (bit_scan_advance__bit_scan mask count_pre bit bit_value
    ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hdouble & Hpositive & Hupper & Hlower_next).
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_3 : concatenating_numbers_dp_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 : concatenating_numbers_dp_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) <> 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  unfold SelectedBitState.
  split; [exact old_PreH19 |].
  split; [exact old_PreH1 |].
  split; [exact Hmaskbit |].
  reflexivity.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 : concatenating_numbers_dp_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) <> 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 : concatenating_numbers_dp_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) <> 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 : concatenating_numbers_dp_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) <> 0)) by annotation_fact.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  rewrite old_PreH2.
  exact Hvalue_small.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 : concatenating_numbers_dp_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : ((Z.land mask bit_value) <> 0)) by annotation_fact.
  assert (old_PreH19 : (BitScanState mask count_pre bit bit_value )) by annotation_fact.

  pose proof (selected_bit_state_from_scan__bit_scan
    mask count_pre bit bit_value ltac:(lia) ltac:(lia) old_PreH19 old_PreH1) as
    (Hbitlt & Hmaskbit & Hland & Hxor & Hvalue_small).
  exact Hbitlt.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_4 : concatenating_numbers_dp_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_5 : concatenating_numbers_dp_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH19 : (DPTablePrefix rows lens count_pre mask choices )) by annotation_fact.

  pose proof old_PreH19 as Hprefix.
  unfold DPTablePrefix in Hprefix.
  destruct Hprefix as [Hzero Hall].
  destruct (Z.eq_dec rest 0) as [Hrest_zero | Hrest_nonzero].
  - Left.
    Exists choices.
    split_pure_spatial.
    + cancel (IntArray.seg (&("best_first")) 0 mask choices).
      cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
      cancel (IntArray.full lengths_pre count_pre lens).
      cancel (IntArray.undef_seg (&("best_first")) mask state_count).
      cancel (IntArray.undef_full result_pre (sum lens)).
    scratch_cancel.
    + split_pures; dump_pre_spatial; auto; try lia.
      * replace (rest - 0) with rest by lia. reflexivity.
      * subst rest. exact Hzero.
  - assert (Hrest_positive : 1 <= rest) by lia.
    assert (Hbest :
      BestIndexForMask rows lens count_pre rest (Znth rest choices 0)).
    { apply Hall. lia. }
    pose proof (proj1 (BestIndexForMask_spec _ _ _ _ _) Hbest)
      as [Hbest_bounds [Hrest_selected Hbest_other]].
    replace (rest - 0) with rest by lia.
    Right.
    Exists choices.
    split_pure_spatial.
    + cancel (IntArray.seg (&("best_first")) 0 mask choices).
      cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
      cancel (IntArray.full lengths_pre count_pre lens).
      cancel (IntArray.undef_seg (&("best_first")) mask state_count).
      cancel (IntArray.undef_full result_pre (sum lens)).
    scratch_cancel.
    + split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 : concatenating_numbers_dp_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH17 : (rest = 0)) by annotation_fact.
  assert (old_PreH21 : (DPTablePrefix rows lens count_pre mask choices_2 )) by annotation_fact.
  assert (old_PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) by annotation_fact.

  eapply
    (dp_table_prefix_extend__dp_table_transition
       rows lens count_pre mask choices_2 bit).
  - lia.
  - lia.
  - exact old_PreH21.
  - lia.
  - eapply
      (best_index_singleton__dp_table_transition
         rows lens count_pre mask bit bit_value rest);
      [lia | exact old_PreH22 | exact old_PreH17].
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 : concatenating_numbers_dp_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_1 : concatenating_numbers_dp_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 : concatenating_numbers_dp_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

  eapply dp_table_prefix_extend__dp_table_transition; eauto; try lia.
  eapply best_index_choose_bit__dp_table_transition; eauto; lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 : concatenating_numbers_dp_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_2 : concatenating_numbers_dp_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 : concatenating_numbers_dp_entail_wit_6_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

  eapply dp_table_prefix_extend__dp_table_transition; eauto; try lia.
  eapply best_index_keep_previous__dp_table_transition
    with (bit := bit) (bit_value := bit_value) (rest := rest) (comparison := retval);
    eauto; lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 : concatenating_numbers_dp_entail_wit_6_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_dp_entail_wit_6_3 : concatenating_numbers_dp_entail_wit_6_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_8 : concatenating_numbers_dp_entail_wit_8.
Proof.
  aggressive_pre_process.
  all: annotation_prepare.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.
  assert (old_PreH11 : ((Zlength rows = count_pre /\ Zlength lens = count_pre /\
     forall i, 0 <= i < count_pre ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.
  assert (old_PreH14 : (DPTablePrefix rows lens count_pre mask choices_2 )) by annotation_fact.

  assert (Hmask : mask = state_count) by lia.
  subst mask.
  rewrite old_PreH2.
  apply greedy_output_full_mask__output_initialization; tauto || lia.
  all: try solve [match goal with
    | H : DPTablePrefix ?r ?l ?c ?old ?table |- DPTablePrefix ?r ?l ?c ?current ?table =>
      replace current with old by lia; exact H end].
  all: try reflexivity.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_9 : concatenating_numbers_dp_entail_wit_9.
Proof.
  unfold concatenating_numbers_dp_entail_wit_10; left; intros.
  annotation_prepare.
  assert (Hbest : BestIndexForMask rows lens count_pre mask (Znth mask choices 0)).
  { destruct PreH25 as [_ Htable]; apply Htable; lia. }
  pose proof (proj1 (BestIndexForMask_spec _ _ _ _ _) Hbest) as [Hindex [Hbit Hgreatest]].
  assert (Hremaining : Zlength output_2 + Znth (Znth mask choices 0) lens 0 <= sum lens).
  { eapply greedy_output_remaining_length__output_initialization; eauto. }
  assert (Hlength : 1 <= Znth (Znth mask choices 0) lens 0 <= number_width_pre).
  { match goal with H : Zlength rows = count_pre /\ Zlength lens = count_pre /\ _ |- _ =>
      destruct H as [_ [_ Hrows]]; specialize (Hrows (Znth mask choices 0) Hindex); tauto end. }
  Exists output_2 output_2 choices.
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try reflexivity.
    unfold AppendRowPrefix.
    change (sublist 0 0 (item_digits (item_at rows lens (Znth mask choices 0)))) with (@nil Z).
    rewrite app_nil_r; reflexivity.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_10_split_goal_1 : concatenating_numbers_dp_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.

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

Lemma proof_of_concatenating_numbers_dp_entail_wit_10 : concatenating_numbers_dp_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_10_split_goal_1.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_11 : concatenating_numbers_dp_entail_wit_11.
Proof.
  LLM_pre_process ltac:(auto).
  all: annotation_prepare.

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
    cancel (IntArray.full (&("best_first")) state_count choices_2).
    cancel (IntArray.seg result_pre 0 (result_length + 1)
      (output_2 +:: Znth (first * number_width_pre + position) flat 0)).
    cancel (IntArray.undef_seg result_pre (result_length + 1) (sum lens)).
    scratch_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_1 : concatenating_numbers_dp_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  all: annotation_prepare.

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

Lemma proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_2 : concatenating_numbers_dp_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  all: annotation_prepare.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.

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
  rewrite Z.shiftl_mul_pow2 in old_PreH2 by lia.
  rewrite Z.mul_1_l in old_PreH2.
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

Lemma proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_3 : concatenating_numbers_dp_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  all: annotation_prepare.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.

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
  rewrite Z.shiftl_mul_pow2 in old_PreH2 by lia.
  rewrite Z.mul_1_l in old_PreH2.
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

Lemma proof_of_concatenating_numbers_dp_entail_wit_12 : concatenating_numbers_dp_entail_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_1.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_2.
  Goal_apply proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_3.

Qed. 

Lemma proof_of_concatenating_numbers_dp_entail_wit_13 : concatenating_numbers_dp_entail_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: annotation_prepare.
  assert (old_PreH1 : (mask = 0)) by annotation_fact.
  assert (old_PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) by annotation_fact.
  assert (old_PreH14 : ((Zlength rows = count_pre /\ Zlength lens = count_pre /\
     forall i, 0 <= i < count_pre ->
       Zlength (Znth i rows nil) = number_width_pre /\
       1 <= Znth i lens 0 <= number_width_pre /\
       1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
       forall j, 0 <= j < Znth i lens 0 ->
         0 <= Znth j (Znth i rows nil) 0 <= 9) )) by annotation_fact.
  assert (old_PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) by annotation_fact.
  assert (old_PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) by annotation_fact.

  - assert (Hgreedy_zero :
        GreedyOutputPrefix rows lens count_pre 0 output_2).
    { rewrite <- old_PreH1; exact old_PreH18. }
    pose proof
      (greedy_output_empty_mask__output_finalization
         rows lens count_pre number_width_pre output_2 old_PreH14 Hgreedy_zero)
      as [Hlargest Houtput_length].
    assert (Hresult_full : result_length = sum lens) by lia.
    assert (Hwidth : Forall (fun row : list Z => Zlength row = number_width_pre) rows).
    { apply decimal_rows_lengths_from_map. assumption. }
    assert (Hflat : FlatRows flat rows count_pre number_width_pre) by assumption.
    assert (Hdata : flat = concat rows).
    { unfold FlatRows in Hflat.
      apply (decimal_rows_concat_unique rows flat count_pre number_width_pre);
        try lia; try tauto; exact Hwidth. }
    Exists output_2.
    split_pure_spatial.
    + rewrite Hresult_full.
      rewrite IntArray.undef_seg_empty.
      sep_apply (IntArray.seg_to_full result_pre 0 (sum lens) output_2).
      replace (result_pre + 0 * sizeof(INT)) with result_pre by lia.
      replace (sum lens - 0) with (sum lens) by lia.
      rewrite <- old_PreH2.
      rewrite Hdata.
      sep_apply (decimal_rows_unflatten rows numbers_pre count_pre number_width_pre
        ltac:(lia) Hwidth ltac:(lia)).
      prop_apply (IntArray.undef_seg_valid (&("best_first")) state_count 1048576).
      Intros_p Hcapacity.
      sep_apply (IntArray.full_to_undef_full (&("best_first")) state_count choices).
      sep_apply (IntArray.undef_full_to_undef_seg (&("best_first")) state_count).
      sep_apply (IntArray.undef_seg_merge_to_undef_full (&("best_first")) 0 state_count 1048576 ltac:(lia)).
      rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r.
      sep_apply (store_int_undef_store_int (&("state_count")) state_count).
      sep_apply (store_int_undef_store_int (&("mask")) mask).
      sep_apply (store_int_undef_store_int (&("result_length")) (sum lens)).
      scratch_cancel; try apply derivable1_refl.
    + dump_pre_spatial; exact Hlargest.

Qed. 

