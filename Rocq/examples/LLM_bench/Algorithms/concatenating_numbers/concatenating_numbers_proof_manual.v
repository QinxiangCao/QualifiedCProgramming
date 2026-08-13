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
From SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers Require Import concatenating_numbers_goal.
From SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers Require Import concatenating_numbers_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.
Local Open Scope sac.

Lemma proof_of_quicksort_numbers_safety_wit_6_split_goal_1 : quicksort_numbers_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold RowsWellFormed in PreH18.
  destruct PreH18 as [_ [_ Hbounds]].
  pose proof (Hbounds scan ltac:(lia)) as Hscan.
  destruct Hscan as [_ [Hscan_length _]].
  lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_6_split_goal_2 : quicksort_numbers_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold RowsWellFormed in PreH18.
  destruct PreH18 as [_ [_ Hbounds]].
  pose proof (Hbounds scan ltac:(lia)) as Hscan.
  destruct Hscan as [_ [Hscan_length _]].
  lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_6 : quicksort_numbers_safety_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_safety_wit_6_split_goal_1.
  Goal_apply proof_of_quicksort_numbers_safety_wit_6_split_goal_2.
Qed. 

Lemma proof_of_quicksort_numbers_safety_wit_19_split_goal_1 : quicksort_numbers_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  subst left_digit.
  subst right_digit.
  pose proof
    (concat_left_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft.
  pose proof
    (concat_right_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hright.
  lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_19_split_goal_2 : quicksort_numbers_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  subst left_digit.
  subst right_digit.
  pose proof
    (concat_left_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft.
  pose proof
    (concat_right_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hright.
  lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_19 : quicksort_numbers_safety_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_safety_wit_19_split_goal_1.
  Goal_apply proof_of_quicksort_numbers_safety_wit_19_split_goal_2.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_1 : quicksort_numbers_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH14 as Hwf.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hrows [Hlens Hentries]].
  specialize (Hentries high_pre ltac:(lia)).
  destruct Hentries as [_ [Hpivot_length _]].
  assert (Hsame_length : Zlength rows = Zlength lens) by lia.
  pose proof
    (PartitionScanState_identity__partition_and_compare_init
       rows lens low_pre high_pre Hsame_length) as Hscan.
  Exists flat rows lens.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hscan.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH18 as Hwf.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hentries]].
  specialize (Hentries scan ltac:(lia)).
  destruct Hentries as [_ [Hscan_length _]].
  pose proof
    (ConcatComparePrefix_zero__partition_and_compare_init
       rows1_2 lens1 scan high_pre) as Hprefix.
  Exists flat1_2 rows1_2 lens1.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_4_split_goal_1 : quicksort_numbers_entail_wit_4_split_goal_1.
Proof.
  unfold quicksort_numbers_entail_wit_4_split_goal_1.
  intros high_v low_v width_v count_v lens_v rows_v flat_v rows1_v
    position_v comparison_v total_v current_v lens1_v pivot_v scan_v
    boundary_v.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
    PreH51 PreH52 PreH53 PreH54.
  assert (Hbound : scan_v * width_v + position_v < count_v * width_v).
  { apply Z.lt_le_trans with ((scan_v + 1) * width_v).
    - rewrite Z.mul_add_distr_r.
      rewrite Z.mul_1_l.
      apply Z.add_lt_mono_l.
      exact PreH6.
    - apply Z.mul_le_mono_nonneg_r.
       + clear - PreH29. lia.
       + clear - PreH33 PreH37. lia. }
  exact Hbound.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_4 : quicksort_numbers_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_4_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_6_split_goal_1 : quicksort_numbers_entail_wit_6_split_goal_1.
Proof.
  unfold quicksort_numbers_entail_wit_6_split_goal_1.
  intros high_v low_v width_v count_v lens_v rows_v flat_v rows1_v
    position_v comparison_v total_v current_v lens1_v pivot_v scan_v
    boundary_v.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
    PreH51 PreH52 PreH53 PreH54.
  apply Z.lt_le_trans with ((high_v + 1) * width_v).
  - rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_l.
    apply Z.add_lt_mono_l.
    exact PreH8.
  - apply Z.mul_le_mono_nonneg_r.
    + clear - PreH29. lia.
    + clear - PreH33. lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_6 : quicksort_numbers_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_6_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_7_1 : quicksort_numbers_entail_wit_7_1.
Proof.
  left.
  intros high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre
    lens rows flat1 rows1_2 position comparison total_length current_length
    lens1_2 pivot_length scan boundary.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
    PreH51 PreH52.
  assert (Hdigit :
    Znth (scan * number_width_pre + position) flat1 0 =
    ConcatLeftDigit rows1_2 lens1_2 scan high_pre position).
  { rewrite (FlatRows_Znth__compare_left_digit
      flat1 rows1_2 count_pre number_width_pre scan position)
      by (try exact PreH52; lia).
    symmetry.
    eapply ConcatLeftDigit_first__compare_left_digit.
    - exact PreH48.
    - lia.
    - rewrite <- PreH39; lia. }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hdigit.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_7_2 : quicksort_numbers_entail_wit_7_2.
Proof.
  left.
  intros high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre
    lens rows flat1 rows1_2 position comparison total_length current_length
    lens1_2 pivot_length scan boundary.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50.
  assert (Hdigit :
    Znth (high_pre * number_width_pre + (position - current_length)) flat1 0 =
    ConcatLeftDigit rows1_2 lens1_2 scan high_pre position).
  {
    rewrite (FlatRows_Znth__compare_left_digit
      flat1 rows1_2 count_pre number_width_pre high_pre
      (position - current_length)) by (try exact PreH50; lia).
    symmetry.
    rewrite PreH37.
    eapply ConcatLeftDigit_second__compare_left_digit.
    - exact PreH46.
    - lia.
    - lia.
    - rewrite <- PreH37, <- PreH36.
      lia.
  }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hdigit.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_9_split_goal_1 : quicksort_numbers_entail_wit_9_split_goal_1.
Proof.
  unfold quicksort_numbers_entail_wit_9_split_goal_1.
  intros high_pre low_pre number_width_pre count_pre lens rows rows1 lens1
    flat1 boundary scan pivot_length current_length total_length comparison
    position left_digit.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
    PreH51 PreH52 PreH53 PreH54 PreH55 PreH56.
  apply Z.lt_le_trans with ((high_pre + 1) * number_width_pre).
  - rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_l.
    apply Z.add_lt_mono_l.
    exact PreH6.
  - apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_9 : quicksort_numbers_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_9_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_11_split_goal_1 : quicksort_numbers_entail_wit_11_split_goal_1.
Proof.
  unfold quicksort_numbers_entail_wit_11_split_goal_1.
  intros high_pre low_pre number_width_pre count_pre lens rows rows1 lens1
    flat1 boundary scan pivot_length current_length total_length comparison
    position left_digit.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
    PreH51 PreH52 PreH53 PreH54 PreH55 PreH56.
  apply Z.lt_le_trans with ((scan + 1) * number_width_pre).
  - rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_l.
    apply Z.add_lt_mono_l.
    exact PreH8.
  - apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_11_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_12_1 : quicksort_numbers_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hright :
    Znth (high_pre * number_width_pre + position) flat1 0 =
      ConcatRightDigit rows1_2 lens1_2 scan high_pre position).
  {
    apply (ConcatRightDigit_first_flat__compare_right_digit
      flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position).
    - exact PreH54.
    - exact PreH50.
    - split; lia.
    - rewrite <- PreH39; lia.
  }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hright.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_12_2 : quicksort_numbers_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hright :
    Znth (scan * number_width_pre + (position - pivot_length)) flat1 0 =
      ConcatRightDigit rows1_2 lens1_2 scan high_pre position).
  {
    rewrite PreH37.
    apply (ConcatRightDigit_second_flat__compare_right_digit
      flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position).
    - exact PreH52.
    - exact PreH48.
    - split; lia.
    - split; lia.
    - rewrite <- PreH37. lia.
    - rewrite <- PreH37, <- PreH38; lia.
  }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hright.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    eapply ConcatComparePrefix_step__compare_outcome; eauto.
    + rewrite <- PreH25, <- PreH26.
      exact PreH1.
    + rewrite (concat_item_digits_Zlength__compare_outcome
                 rows1_2 lens1_2 count_pre number_width_pre scan high_pre);
        eauto; lia.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_14_1 : quicksort_numbers_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    sep_apply (store_int_undef_store_int (&( "position" )) position).
    cancel ((( &( "position" ) )) # Int |->_).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    rewrite PreH22.
    eapply ConcatCompareOutcome_zero__compare_outcome.
    + exact PreH27.
    + rewrite (concat_item_digits_Zlength__compare_outcome
                 rows1_2 lens1_2 count_pre number_width_pre scan high_pre).
      * rewrite <- PreH16, <- PreH15; lia.
      * exact PreH25.
      * lia.
      * lia.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_14_2 : quicksort_numbers_entail_wit_14_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    sep_apply (store_int_undef_store_int (&( "position" )) position).
    cancel ((( &( "position" ) )) # Int |->_).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    replace (left_digit - right_digit) with
      (ConcatLeftDigit rows1_2 lens1_2 scan high_pre position -
       ConcatRightDigit rows1_2 lens1_2 scan high_pre position) by congruence.
    eapply ConcatCompareOutcome_difference__compare_outcome.
    + exact PreH29.
    + rewrite (concat_item_digits_Zlength__compare_outcome
                 rows1_2 lens1_2 count_pre number_width_pre scan high_pre).
      * rewrite <- PreH16, <- PreH15; lia.
      * exact PreH27.
      * lia.
      * lia.
    + rewrite <- PreH25, <- PreH26.
      exact PreH1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_15 : quicksort_numbers_entail_wit_15.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1 rows1 rows1 lens1_2.
  split_pure_spatial.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try reflexivity;
      first
        [ replace (boundary + 1 - 1) with boundary by lia; exact PreH23
        | eapply SwapRowsPrefix_zero__scan_row_swap with
            (lens := lens1_2) (count := count_pre); eauto; try lia;
          replace (boundary + 1 - 1) with boundary by lia; assumption ].
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_16_split_goal_1 : quicksort_numbers_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hboundary_count : boundary < count_pre) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hboundary_mul :
    boundary * number_width_pre <=
    (count_pre - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count_pre * number_width_pre) with
    ((count_pre - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_16 : quicksort_numbers_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_16_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_17_split_goal_1 : quicksort_numbers_entail_wit_17_split_goal_1.
Proof.
  unfold quicksort_numbers_entail_wit_17_split_goal_1.
  intros high_pre low_pre number_width_pre count_pre lens rows flat_now
    rows_now comparison rows_before lens1 pivot_length column scan boundary.
  intros PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    PreH41 PreH42 PreH43 PreH44 PreH45.
  apply Z.lt_le_trans with ((scan + 1) * number_width_pre).
  - rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_l.
    apply Z.add_lt_mono_l.
    exact PreH21.
  - apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_17 : quicksort_numbers_entail_wit_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_17_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_18 : quicksort_numbers_entail_wit_18.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH35 as Hwf_copy.
  destruct Hwf_copy as [Hbefore_len [Hlens_len Hrow_wf]].
  pose proof (Hrow_wf boundary ltac:(lia)) as [Hboundary_len _].
  pose proof (Hrow_wf scan ltac:(lia)) as [Hscan_len _].
  assert (Hstep : exists rows_next,
    FlatRows
      (replace_Znth (scan * number_width_pre + column)
        (Znth (boundary * number_width_pre + column) flat_now_2 0)
        (replace_Znth (boundary * number_width_pre + column)
          (Znth (scan * number_width_pre + column) flat_now_2 0) flat_now_2))
      rows_next count_pre number_width_pre /\
    SwapRowsPrefix rows_before_2 rows_next boundary scan
      (column + 1) number_width_pre).
  {
    eapply FlatRows_swap_progress_step__scan_row_swap with
      (flat := flat_now_2) (before := rows_before_2) (now := rows_now_2)
      (count := count_pre) (width := number_width_pre)
      (first := boundary) (second := scan) (progress := column).
    all: try assumption; try lia.
  }
  destruct Hstep as [rows_next [Hflat_next Hswap_next]].
  Exists
    (replace_Znth (scan * number_width_pre + column)
       (Znth (boundary * number_width_pre + column) flat_now_2 0)
       (replace_Znth (boundary * number_width_pre + column)
          (Znth (scan * number_width_pre + column) flat_now_2 0) flat_now_2))
    rows_next rows_before_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hswap_next;
      try exact Hflat_next.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_19_1 : quicksort_numbers_entail_wit_19_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcolumn : column = number_width_pre) by lia.
  assert (Hrows_now : rows_now = swap_Znth nil boundary scan rows_before).
  {
    eapply SwapRowsPrefix_complete__scan_advance; eauto; lia.
  }
  assert (Hsum_after :
    sum
      (replace_Znth scan (Znth boundary lens1_2 0)
        (replace_Znth boundary (Znth scan lens1_2 0) lens1_2)) =
    sum lens).
  {
    unfold swap_Znth.
    rewrite <- PreH24.
    apply sum_permutation__scan_advance.
    apply Permutation_sym.
    apply permutation_swap_Znth__scan_advance;
      unfold RowsWellFormed in PreH19; lia.
  }
  assert (Hpartition_after :
    PartitionScanState rows rows_now lens
      (replace_Znth scan (Znth boundary lens1_2 0)
        (replace_Znth boundary (Znth scan lens1_2 0) lens1_2))
      low_pre high_pre boundary (scan + 1)).
  {
    rewrite Hrows_now.
    unfold swap_Znth.
    eapply PartitionScanState_swap_advance__scan_advance; eauto; lia.
  }
  assert (Hwell_after :
    RowsWellFormed rows_now
      (replace_Znth scan (Znth boundary lens1_2 0)
        (replace_Znth boundary (Znth scan lens1_2 0) lens1_2))
      count_pre number_width_pre).
  {
    rewrite Hrows_now.
    unfold swap_Znth.
    eapply RowsWellFormed_swap_Znth__scan_advance; eauto; lia.
  }
  assert (Hpivot_after :
    pivot_length =
      Znth high_pre
        (replace_Znth scan (Znth boundary lens1_2 0)
          (replace_Znth boundary (Znth scan lens1_2 0) lens1_2)) 0).
  {
    unfold RowsWellFormed in PreH19.
    destruct PreH19 as [Hrowslen [Hlenslen Hall]].
    rewrite Znth_replace_Znth_Diff.
    - rewrite Znth_replace_Znth_Diff.
      + exact PreH16.
      + rewrite Hlenslen; lia.
      + rewrite Hlenslen; lia.
      + lia.
    - rewrite Zlength_replace_Znth, Hlenslen; lia.
    - rewrite Zlength_replace_Znth, Hlenslen; lia.
    - lia.
  }
  Exists flat_now rows_now
    (replace_Znth scan (Znth boundary lens1_2 0)
      (replace_Znth boundary (Znth scan lens1_2 0) lens1_2)).
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat_now).
    cancel (IntArray.full lengths_pre count_pre
      (replace_Znth scan (Znth boundary lens1_2 0)
        (replace_Znth boundary (Znth scan lens1_2 0) lens1_2))).
    apply store_int_undef_store_int.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hpivot_after;
      try exact Hwell_after; try exact Hpartition_after; try exact Hsum_after.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_19_2 : quicksort_numbers_entail_wit_19_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat sep_apply store_int_undef_store_int.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply PartitionScanState_advance_nonbefore__scan_advance; [exact PreH23 |].
    eapply ConcatCompareOutcome_nonpositive_not_item_before__scan_advance; eauto.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_20 : quicksort_numbers_entail_wit_20.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_21 : quicksort_numbers_entail_wit_21.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hscan : scan = high_pre) by lia.
  subst scan.
  Exists flat1 rows1 rows1 lens1_2.
  split_pure_spatial.
  - repeat sep_apply store_int_undef_store_int.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try reflexivity.
      first
        [ replace (boundary + 1 - 1) with boundary by lia; exact PreH19
        | eapply SwapRowsPrefix_zero__scan_advance; eauto; lia ].
  eapply SwapRowsPrefix_zero__scan_advance; eauto; lia.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_22_split_goal_1 : quicksort_numbers_entail_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpivot_count : pivot < count_pre) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hpivot_mul :
    pivot * number_width_pre <=
    (count_pre - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count_pre * number_width_pre) with
    ((count_pre - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_22 : quicksort_numbers_entail_wit_22.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_22_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_23_split_goal_1 : quicksort_numbers_entail_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hhigh_count : high_pre < count_pre) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hhigh_mul :
    high_pre * number_width_pre <=
    (count_pre - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count_pre * number_width_pre) with
    ((count_pre - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_23 : quicksort_numbers_entail_wit_23.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_entail_wit_23_split_goal_1.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_24 : quicksort_numbers_entail_wit_24.
Proof.
  right.
  intros.
  pose proof PreH30 as Hwell_formed.
  unfold RowsWellFormed in Hwell_formed.
  destruct Hwell_formed as
    (Hbefore_len & Hlens_len & Hrow_well_formed).
  pose proof (Hrow_well_formed pivot ltac:(lia)) as Hpivot_well_formed.
  pose proof (Hrow_well_formed high_pre ltac:(lia)) as Hhigh_well_formed.
  destruct Hpivot_well_formed as (Hpivot_row_len & _).
  destruct Hhigh_well_formed as (Hhigh_row_len & _).
  pose proof PreH34 as Hflat_shape.
  unfold FlatRows in Hflat_shape.
  destruct Hflat_shape as
    (Hflat_len & Hrows_now_len & Hflat_rows).
  pose proof (FlatRows_Znth_cell__pivot_finalization
    flat_now_2 rows_now_2 count_pre number_width_pre
    pivot column PreH34 ltac:(lia) ltac:(lia)) as Hpivot_cell.
  pose proof (FlatRows_Znth_cell__pivot_finalization
    flat_now_2 rows_now_2 count_pre number_width_pre
    high_pre column PreH34 ltac:(lia) ltac:(lia)) as Hhigh_cell.
  destruct (Z.eq_dec pivot high_pre) as [Hpivot_high | Hpivot_high].
  - subst pivot.
    assert (Hrows_same : rows_now_2 = rows_before_2).
    {
      eapply SwapRowsPrefix_same_current__pivot_finalization;
        eauto; lia.
    }
    assert (Hswap_next :
      SwapRowsPrefix rows_before_2 rows_now_2 high_pre high_pre
        (column + 1) number_width_pre).
    {
      rewrite Hrows_same.
      apply SwapRowsPrefix_same_refl__pivot_finalization;
        eauto; lia.
    }
    rewrite replace_Znth_twice__pivot_finalization.
    rewrite replace_Znth_Znth.
    LLM_pre_process ltac:(int_auto).
    Exists rows_now_2 rows_before_2.
    repeat (split_pure_spatial || split_pures); try cancel;
      dump_pre_spatial; auto; try lia; try exact Hswap_next; try exact PreH34.
  - assert (Hpivot_high_lt : pivot < high_pre) by lia.
    set (flat_first :=
      replace_Znth (pivot * number_width_pre + column)
        (Znth (high_pre * number_width_pre + column) flat_now_2 0)
        flat_now_2).
    set (rows_first :=
      replace_Znth pivot
        (replace_Znth column
          (Znth (high_pre * number_width_pre + column) flat_now_2 0)
          (Znth pivot rows_now_2 nil))
        rows_now_2).
    set (flat_after :=
      replace_Znth (high_pre * number_width_pre + column)
        (Znth (pivot * number_width_pre + column) flat_now_2 0)
        flat_first).
    set (rows_after :=
      replace_Znth high_pre
        (replace_Znth column
          (Znth (pivot * number_width_pre + column) flat_now_2 0)
          (Znth high_pre rows_first nil))
        rows_first).
    assert (Hflat_first :
      FlatRows flat_first rows_first count_pre number_width_pre).
    {
      unfold flat_first, rows_first.
      eapply FlatRows_replace_cell__pivot_finalization;
        eauto; lia.
    }
    assert (Hflat_after :
      FlatRows flat_after rows_after count_pre number_width_pre).
    {
      unfold flat_after, rows_after.
      eapply FlatRows_replace_cell__pivot_finalization;
        eauto; lia.
    }
    assert (Hswap_after :
      SwapRowsPrefix rows_before_2 rows_after pivot high_pre
        (column + 1) number_width_pre).
    {
      unfold rows_after, rows_first.
      rewrite Hhigh_cell, Hpivot_cell.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrows_now_len; lia).
      eapply SwapRowsPrefix_advance_distinct__pivot_finalization;
        eauto; lia.
    }
    LLM_pre_process ltac:(int_auto).
    Exists rows_after rows_before_2.
    fold flat_first.
    fold flat_after.
    repeat (split_pure_spatial || split_pures); try cancel;
      dump_pre_spatial; auto; try lia; try exact Hswap_after; try exact Hflat_after.
Qed. 

Lemma proof_of_quicksort_numbers_entail_wit_25 : quicksort_numbers_entail_wit_25.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcolumn_done : column = number_width_pre) by lia.
  subst column.
  pose proof PreH18 as Hwell_formed.
  unfold RowsWellFormed in Hwell_formed.
  destruct Hwell_formed as
    (Hrows_before_len & Hlens_before_len & Hrow_well_formed).
  pose proof (Hrow_well_formed pivot ltac:(lia)) as Hpivot_well_formed.
  pose proof (Hrow_well_formed high_pre ltac:(lia)) as Hhigh_well_formed.
  destruct Hpivot_well_formed as (Hpivot_row_len & _).
  destruct Hhigh_well_formed as (Hhigh_row_len & _).
  assert (Hrows_swap :
    rows_now = swap_Znth nil pivot high_pre rows_before).
  {
    eapply SwapRowsPrefix_complete__pivot_finalization;
      eauto.
  }
  set (lens_after :=
    replace_Znth pivot pivot_length
      (replace_Znth high_pre (Znth pivot lens1_2 0) lens1_2)).
  assert (Hlens_swap :
    lens_after = swap_Znth 0 pivot high_pre lens1_2).
  {
    unfold lens_after.
    rewrite PreH15.
    apply swap_Znth_reverse__pivot_finalization; lia.
  }
  assert (Hwell_formed_after :
    RowsWellFormed rows_now lens_after count_pre number_width_pre).
  {
    rewrite Hrows_swap, Hlens_swap.
    eapply RowsWellFormed_swap__pivot_finalization;
      eauto; lia.
  }
  pose proof PreH19 as Hstate_parts.
  unfold PartitionScanState in Hstate_parts.
  destruct Hstate_parts as
    (Hpaired_before & Houtside_before & Hhigh_same &
     Hbefore_pivot & Hafter_pivot).
  assert (Hpaired_after :
    PairedPermutation rows rows_now lens lens_after).
  {
    rewrite Hrows_swap, Hlens_swap.
    apply PairedPermutation_swap__pivot_finalization.
    - exact Hpaired_before.
    - rewrite Hrows_before_len, Hlens_before_len. reflexivity.
    - rewrite Hrows_before_len. lia.
    - rewrite Hrows_before_len. lia.
  }
  assert (Houtside_after :
    SameOutsidePairedRange rows rows_now lens lens_after
      low_pre high_pre).
  {
    rewrite Hrows_swap, Hlens_swap.
    apply SameOutsidePairedRange_swap_inside__pivot_finalization.
    - exact Houtside_before.
    - rewrite Hrows_before_len, Hlens_before_len. reflexivity.
    - rewrite Hrows_before_len. lia.
    - rewrite Hrows_before_len. lia.
    - lia.
    - lia.
  }
  assert (Hpartitioned_after :
    GreedyPartitionedAt rows_now lens_after low_pre high_pre pivot).
  {
    rewrite Hrows_swap, Hlens_swap.
    eapply PartitionScanState_finalize__pivot_finalization;
      eauto; lia.
  }
  assert (Hsum_after : sum lens_after = sum lens).
  {
    rewrite Hlens_swap.
    rewrite sum_swap_Znth__pivot_finalization.
    - exact PreH21.
    - rewrite Hlens_before_len. lia.
    - rewrite Hlens_before_len. lia.
  }
  Exists flat_now rows_now lens_after.
  split_pure_spatial.
  - cancel (IntArray.full lengths_pre count_pre lens_after).
    cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat_now).
    apply store_int_undef_store_int.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hpartitioned_after;
      try exact Hsum_after.
Qed. 

Lemma proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_3 rows1_3 lens1_3.
  assert (Hpart2 : GreedyPartitionedAt
        rows2 lens2 low_pre high_pre pivot).
  {
    eapply greedy_partitioned_preserved_left__quicksort_range_composition;
      try exact PreH8; try exact PreH10; try exact PreH11;
      try exact PreH29; lia.
  }
  assert (Hpart13 : GreedyPartitionedAt
        rows1_3 lens1_3 low_pre high_pre pivot).
  {
    eapply greedy_partitioned_preserved_right__quicksort_range_composition;
      try exact PreH1; try exact PreH3; try exact PreH4;
      try exact Hpart2; lia.
  }
  assert (Hleft13 : GreedySortedRange
        rows1_3 lens1_3 low_pre (pivot - 1)).
  {
    eapply greedy_sorted_range_preserved_outside__quicksort_range_composition
      with (rows0 := rows2) (lens0 := lens2)
           (change_left := pivot + 1) (change_right := high_pre).
    + exact PreH4.
    + lia.
    + destruct PreH8 as [Hrows13 _]. rewrite Hrows13. lia.
    + intros k Hk. left. lia.
    + exact PreH12.
  }
  assert (Hsum13 : sum lens1_3 = sum lens) by lia.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      first
        [ eapply greedy_sorted_range_combine__quicksort_range_composition;
          try exact PreH1; try exact Hpart13; try exact Hleft13;
          try exact PreH5; lia
        | eapply same_outside_paired_range_trans__quicksort_range_composition;
          [ exact PreH28
          | eapply same_outside_paired_range_trans__quicksort_range_composition;
            [ eapply same_outside_paired_range_weaken__quicksort_range_composition;
              try exact PreH11; lia
            | eapply same_outside_paired_range_weaken__quicksort_range_composition;
              try exact PreH4; lia ] ]
        | eapply paired_permutation_trans__quicksort_range_composition;
          [ exact PreH27
          | eapply paired_permutation_trans__quicksort_range_composition; eauto ] ].
Qed. 

Lemma proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat2 rows2 lens2.
  assert (Hpart2 : GreedyPartitionedAt
        rows2 lens2 low_pre high_pre pivot).
  {
    eapply (greedy_partitioned_preserved_left__quicksort_range_composition
      rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre
      low_pre high_pre pivot);
      try exact PreH2; try exact PreH4; try exact PreH5;
      try exact PreH23; lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      first
        [ eapply greedy_sorted_range_combine__quicksort_range_composition;
          try exact PreH2; try exact Hpart2; try exact PreH6; try lia;
          apply greedy_sorted_range_base__quicksort_range_composition; lia
        | eapply same_outside_paired_range_trans__quicksort_range_composition;
          [ exact PreH22
          | eapply same_outside_paired_range_weaken__quicksort_range_composition;
            try exact PreH5; lia ]
        | eapply paired_permutation_trans__quicksort_range_composition; eauto ].
Qed. 

Lemma proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_3 rows1_3 lens1_3.
  assert (Hpart3 : GreedyPartitionedAt
        rows1_3 lens1_3 low_pre high_pre pivot).
  {
    eapply (greedy_partitioned_preserved_right__quicksort_range_composition
      rows1_2 rows1_3 lens1_2 lens1_3 count_pre number_width_pre
      low_pre high_pre pivot);
      try exact PreH1; try exact PreH3; try exact PreH4;
      try exact PreH23; lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      first
        [ eapply greedy_sorted_range_combine__quicksort_range_composition;
          try exact PreH1; try exact Hpart3; try exact PreH5; try lia;
          apply greedy_sorted_range_base__quicksort_range_composition; lia
        | eapply same_outside_paired_range_trans__quicksort_range_composition;
          [ exact PreH22
          | eapply same_outside_paired_range_weaken__quicksort_range_composition;
            try exact PreH4; lia ]
        | eapply paired_permutation_trans__quicksort_range_composition; eauto ].
Qed. 

Lemma proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat rows lens.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      first
        [ apply greedy_sorted_range_base__quicksort_range_composition; lia
        | apply same_outside_paired_range_refl__quicksort_range_composition
        | apply paired_permutation_refl__quicksort_range_composition;
          destruct PreH13 as [Hrows [Hlens _]]; lia ].
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_1_1 : concatenating_numbers_entail_wit_1_1.
Proof.
  left.
  intros.
  assert (Hsorted : GreedySorted rows1_2 lens1_2).
  {
    unfold GreedySorted.
    intros x y [Hx [Hxy Hy]].
    apply PreH5.
    pose proof PreH1 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrows_len _].
    rewrite Hrows_len in Hy.
    lia.
  }
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    cancel (IntArray.undef_full result_pre (sum lens)).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hsorted.
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_1_2 : concatenating_numbers_entail_wit_1_2.
Proof.
  left.
  intros.
  assert (Hcount : count_pre = 1) by lia.
  assert (Hperm : PairedPermutation rows rows lens lens).
  { unfold PairedPermutation.
    pose proof PreH8 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrows [Hlens _]].
    repeat split; try lia.
    apply Permutation_refl. }
  assert (Hsorted : GreedySorted rows lens).
  { unfold GreedySorted.
    intros x y [Hx [Hxy Hy]].
    pose proof PreH8 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrows _].
    rewrite Hrows, Hcount in Hy.
    assert (x = 0 /\ y = 0) by lia.
    destruct H as [-> ->].
    unfold item_before_or_equal, digit_lex_ge.
    split; [reflexivity | left; reflexivity]. }
  Exists flat rows lens.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
    cancel (IntArray.full lengths_pre count_pre lens).
    cancel (IntArray.undef_full result_pre (sum lens)).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hperm; try exact Hsorted.
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_2 : concatenating_numbers_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 (@nil Z) rows1_2 lens1_2.
  rewrite ConcatenatedPrefix_zero__output_setup.
  subst result_length.
  sep_apply_l_atomic
    (IntArray.undef_full_to_undef_seg result_pre (sum lens)).
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    cancel (IntArray.undef_seg result_pre 0 (sum lens)).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlens_i : 1 <= Znth i lens1_2 0 <= number_width_pre).
  { pose proof PreH10 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [_ [_ Hrows]].
    specialize (Hrows i ltac:(lia)).
    tauto. }
  assert (Houtput :
      output_2 = ConcatenatedOutputPrefix rows1_2 lens1_2 i 0).
  { rewrite ConcatenatedOutputPrefix_zero__output_setup.
    exact PreH14. }
  Exists flat1_2 output_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    cancel (IntArray.seg result_pre 0 result_length output_2).
    cancel (IntArray.undef_seg result_pre result_length (sum lens)).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Houtput; try exact Hlens_i.
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_4_split_goal_1 : concatenating_numbers_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  assert (Hi_count : i < count_pre) by lia.
  assert (Hwidth_pos : 0 < number_width_pre) by lia.
  assert (Hi_mul :
    i * number_width_pre <= (count_pre - 1) * number_width_pre).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  replace (count_pre * number_width_pre) with
    ((count_pre - 1) * number_width_pre + number_width_pre) by ring.
  lia.
Qed.

Lemma proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_entail_wit_4_split_goal_1.
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_5_split_goal_1 : concatenating_numbers_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH31, PreH30.
  rewrite <- PreH29.
  apply (ConcatenatedOutputPrefix_lt_sum__output_inner_loop
           rows1 lens1 count_pre number_width_pre i j PreH26); lia.
Qed.

Lemma proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_concatenating_numbers_entail_wit_5_split_goal_1.
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_6 : concatenating_numbers_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2
    (output_2 ++ Znth (i * number_width_pre + j) flat1_2 0 :: nil)
    rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      first
        [ rewrite Zlength_app; rewrite <- PreH33; simpl; reflexivity
        | rewrite PreH32;
          apply (ConcatenatedOutputPrefix_append__output_inner_loop
                   flat1_2 rows1_2 lens1_2 count_pre number_width_pre i j
                   PreH36 PreH28); lia ].
Qed. 

Lemma proof_of_concatenating_numbers_entail_wit_7 : concatenating_numbers_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists flat1_2 output_2 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    assert (Hj : j = Znth i lens1_2 0) by lia.
    rewrite PreH18, Hj.
    eapply ConcatenatedOutputPrefix_full_row__output_inner_loop; eauto; lia.
Qed. 

Lemma proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  - assert (Hi_eq : i = count_pre) by lia.
    assert (Houtput_eq :
      output_2 = concatenate_rows rows1_2 lens1_2).
    { rewrite PreH14, Hi_eq.
      apply ConcatenatedPrefix_full__largest_concatenation_final
        with (width := number_width_pre).
      exact PreH10. }
    assert (Houtput_len : Zlength output_2 = sum lens).
    { rewrite Houtput_eq.
      rewrite (RowsWellFormed_concatenate_rows_length__largest_concatenation_final
                 rows1_2 lens1_2 count_pre number_width_pre PreH10).
      exact PreH13. }
    assert (Hresult_full : result_length = sum lens) by lia.
    assert (Hlargest :
      LargestConcatenation rows rows1_2 lens lens1_2 output_2).
    { rewrite Houtput_eq.
      eapply GreedySorted_LargestConcatenation__largest_concatenation_final;
        eauto. }
    Exists output_2. Exists flat1_2. Exists rows1_2. Exists lens1_2.
    split_pure_spatial.
    + rewrite Hresult_full.
      rewrite IntArray.undef_seg_empty.
      sep_apply (IntArray.seg_to_full result_pre 0 (sum lens) output_2).
      replace (result_pre + 0 * sizeof(INT)) with result_pre by lia.
      replace (sum lens - 0) with (sum lens) by lia.
      cancel.
    + split_pures; dump_pre_spatial; auto.
Qed. 
