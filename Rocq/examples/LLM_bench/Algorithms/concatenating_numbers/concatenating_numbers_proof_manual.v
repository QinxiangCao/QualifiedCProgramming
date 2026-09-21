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


Ltac annotation_wf :=
  first [assumption |
    apply (proj2 (RowsWellFormed_explicit__annotation _ _ _ _));
      repeat split; assumption |
    match goal with
    | H : PairedPermutation ?r0 ?r1 ?l0 ?l1 |- RowsWellFormed ?r1 ?l1 ?c ?w =>
      let Hw := fresh "Hwf_source" in
      assert (Hw : RowsWellFormed r0 l0 c w) by annotation_wf;
      exact (proj1 (RowsWellFormed_permutation__annotation r0 r1 l0 l1 c w Hw H))
    end].

Ltac annotation_domains :=
  repeat match goal with
  | H : PairedPermutation _ _ _ _ |- _ =>
    let E := fresh "Hsum" in
    pose proof (sum_permutation__scan_advance _ _
      (proj1 (proj2 (PairedPermutation_projections__annotation _ _ _ _ H)))) as E;
    revert H
  end; intros;
  repeat match goal with
  | H : RowsWellFormed _ _ _ _ |- _ =>
    let E := fresh "Hdomain" in
    pose proof (proj1 (RowsWellFormed_explicit__annotation _ _ _ _) H) as E;
    repeat match type of E with
    | _ /\ _ => let E1 := fresh "Hdomain" in destruct E as [E1 E]
    end;
    revert H
  end; intros.

Ltac annotation_fact :=
  first [assumption | annotation_wf |
    solve [annotation_domains; auto; try lia; try nia] ].
Lemma proof_of_concatenating_numbers_entail_wit_1 : concatenating_numbers_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwidth : Forall (fun row : list Z => Zlength row = number_width_pre) rows).
  { apply decimal_rows_lengths_from_map. assumption. }
  subst flat.
  sep_apply (decimal_rows_flatten rows numbers_pre count_pre number_width_pre ltac:(lia) ltac:(lia)).
  split_pure_spatial.
  - repeat cancel; try apply derivable1_refl.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold FlatRows. split.
    + rewrite decimal_rows_flat_length with (width := number_width_pre) by exact Hwidth. lia.
    + split; [assumption |]. intros k Hk.
      apply decimal_rows_flat_row; try assumption; lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_6_split_goal_1 : quicksort_numbers_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre )) by annotation_fact.
  dump_pre_spatial.
  unfold RowsWellFormed in old_PreH18.
  destruct old_PreH18 as [_ [_ Hbounds]].
  pose proof (Hbounds scan ltac:(lia)) as Hscan.
  destruct Hscan as [_ [Hscan_length _]].
  lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_6_split_goal_2 : quicksort_numbers_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre )) by annotation_fact.
  dump_pre_spatial.
  unfold RowsWellFormed in old_PreH18.
  destruct old_PreH18 as [_ [_ Hbounds]].
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
  assert (old_PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre )) by annotation_fact.
  dump_pre_spatial.
  subst left_digit.
  subst right_digit.
  pose proof
    (concat_left_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       old_PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft.
  pose proof
    (concat_right_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       old_PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hright.
  lia.
Qed.

Lemma proof_of_quicksort_numbers_safety_wit_19_split_goal_2 : quicksort_numbers_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre )) by annotation_fact.
  dump_pre_spatial.
  subst left_digit.
  subst right_digit.
  pose proof
    (concat_left_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       old_PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft.
  pose proof
    (concat_right_digit_bounds__safety_arithmetic
       rows1 lens1 count_pre number_width_pre scan high_pre position
       old_PreH27 ltac:(lia) ltac:(lia) ltac:(lia)) as Hright.
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
  assert (old_PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) by annotation_fact.
  pose proof old_PreH14 as Hwf.
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
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hscan.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH18 : (RowsWellFormed rows1_2 lens1 count_pre number_width_pre )) by annotation_fact.
  pose proof old_PreH18 as Hwf.
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
  - split_pures; dump_pre_spatial; auto; try annotation_fact.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_3_1 : quicksort_numbers_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH39 : (current_length = (Znth (scan) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) by annotation_fact.
  assert (Hdigit :
    Znth (scan * number_width_pre + position) flat1 0 =
    ConcatLeftDigit rows1_2 lens1_2 scan high_pre position).
  { rewrite (FlatRows_Znth__compare_left_digit
      flat1 rows1_2 count_pre number_width_pre scan position)
      by (try exact old_PreH52; lia).
    symmetry.
    eapply ConcatLeftDigit_first__compare_left_digit.
    - exact old_PreH48.
    - lia.
    - rewrite <- old_PreH39; lia. }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hdigit.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_3_2 : quicksort_numbers_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH36 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH37 : (current_length = (Znth (scan) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH46 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH50 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) by annotation_fact.
  assert (Hdigit :
    Znth (high_pre * number_width_pre + (position - current_length)) flat1 0 =
    ConcatLeftDigit rows1_2 lens1_2 scan high_pre position).
  {
    rewrite (FlatRows_Znth__compare_left_digit
      flat1 rows1_2 count_pre number_width_pre high_pre
      (position - current_length)) by (try exact old_PreH50; lia).
    symmetry.
    rewrite old_PreH37.
    eapply ConcatLeftDigit_second__compare_left_digit.
    - exact old_PreH46.
    - lia.
    - lia.
    - rewrite <- old_PreH37, <- old_PreH36.
      lia.
  }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hdigit.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_4_1 : quicksort_numbers_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH39 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH50 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH54 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) by annotation_fact.
  assert (Hright :
    Znth (high_pre * number_width_pre + position) flat1 0 =
      ConcatRightDigit rows1_2 lens1_2 scan high_pre position).
  {
    apply (ConcatRightDigit_first_flat__compare_right_digit
      flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position).
    - exact old_PreH54.
    - exact old_PreH50.
    - split; lia.
    - rewrite <- old_PreH39; lia.
  }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hright.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_4_2 : quicksort_numbers_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH37 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH38 : (current_length = (Znth (scan) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) by annotation_fact.
  assert (Hright :
    Znth (scan * number_width_pre + (position - pivot_length)) flat1 0 =
      ConcatRightDigit rows1_2 lens1_2 scan high_pre position).
  {
    rewrite old_PreH37.
    apply (ConcatRightDigit_second_flat__compare_right_digit
      flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position).
    - exact old_PreH52.
    - exact old_PreH48.
    - split; lia.
    - split; lia.
    - rewrite <- old_PreH37. lia.
    - rewrite <- old_PreH37, <- old_PreH38; lia.
  }
  Exists flat1 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hright.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_5 : quicksort_numbers_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH1 : (left_digit = right_digit)) by annotation_fact.
  assert (old_PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) by annotation_fact.
  assert (old_PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) by annotation_fact.
  assert (old_PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try annotation_fact.
    eapply ConcatComparePrefix_step__compare_outcome; eauto.
    + rewrite <- old_PreH25, <- old_PreH26.
      exact old_PreH1.
    + rewrite (concat_item_digits_Zlength__compare_outcome
                 rows1_2 lens1_2 count_pre number_width_pre scan high_pre);
        eauto; lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_6_1 : quicksort_numbers_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH16 : (current_length = (Znth (scan) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH22 : (comparison = 0)) by annotation_fact.
  assert (old_PreH25 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH27 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) by annotation_fact.
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    sep_apply (store_int_undef_store_int (&( "position" )) position).
    cancel ((( &( "position" ) )) # Int |->_).
  - split_pures.
    all: dump_pre_spatial; try assumption; try annotation_fact.
    rewrite old_PreH22.
    eapply ConcatCompareOutcome_zero__compare_outcome.
    + exact old_PreH27.
    + rewrite (concat_item_digits_Zlength__compare_outcome
                 rows1_2 lens1_2 count_pre number_width_pre scan high_pre).
      * rewrite <- old_PreH16, <- old_PreH15; lia.
      * exact old_PreH25.
      * lia.
      * lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_6_2 : quicksort_numbers_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH1 : (left_digit <> right_digit)) by annotation_fact.
  assert (old_PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH16 : (current_length = (Znth (scan) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) by annotation_fact.
  assert (old_PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) by annotation_fact.
  assert (old_PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) by annotation_fact.
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    sep_apply (store_int_undef_store_int (&( "position" )) position).
    cancel ((( &( "position" ) )) # Int |->_).
  - split_pures.
    all: dump_pre_spatial; try assumption; try annotation_fact.
    replace (left_digit - right_digit) with
      (ConcatLeftDigit rows1_2 lens1_2 scan high_pre position -
       ConcatRightDigit rows1_2 lens1_2 scan high_pre position) by congruence.
    eapply ConcatCompareOutcome_difference__compare_outcome; [lia | | |].
    + exact old_PreH29.
    + rewrite (concat_item_digits_Zlength__compare_outcome
                 rows1_2 lens1_2 count_pre number_width_pre scan high_pre).
      * rewrite <- old_PreH16, <- old_PreH15; lia.
      * exact old_PreH27.
      * lia.
      * lia.
    + rewrite <- old_PreH25, <- old_PreH26.
      exact old_PreH1.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_7 : quicksort_numbers_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH22 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH23 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan )) by annotation_fact.
  Exists flat1 rows1 rows1 lens1_2.
  split_pure_spatial.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try reflexivity;
      first
        [ replace (boundary + 1 - 1) with boundary by lia; exact old_PreH23
        | eapply SwapRowsPrefix_zero__scan_row_swap with
            (lens := lens1_2) (count := count_pre); eauto; try annotation_fact;
          replace (boundary + 1 - 1) with boundary by lia; assumption ].
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_8 : quicksort_numbers_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH35 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  pose proof old_PreH35 as Hwf_copy.
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
    all: try assumption; try annotation_fact.
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
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hswap_next;
      try exact Hflat_next.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_9_1 : quicksort_numbers_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH16 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH19 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH24 : ((sum (lens1_2)) = (sum (lens)))) by annotation_fact.
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
    rewrite <- old_PreH24.
    apply sum_permutation__scan_advance.
    apply Permutation_sym.
    apply permutation_swap_Znth__scan_advance;
      unfold RowsWellFormed in old_PreH19; lia.
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
    unfold RowsWellFormed in old_PreH19.
    destruct old_PreH19 as [Hrowslen [Hlenslen Hall]].
    rewrite Znth_replace_Znth_Diff.
    - rewrite Znth_replace_Znth_Diff.
      + exact old_PreH16.
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
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hpivot_after;
      try exact Hwell_after; try exact Hpartition_after; try exact Hsum_after.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_9_2 : quicksort_numbers_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH22 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH23 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) by annotation_fact.
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat sep_apply store_int_undef_store_int.
    cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact.
    eapply PartitionScanState_advance_nonbefore__scan_advance; [exact old_PreH23 |].
    eapply ConcatCompareOutcome_nonpositive_not_item_before__scan_advance; eauto.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_10 : quicksort_numbers_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH16 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  Exists flat1_2 rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH18 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH19 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan )) by annotation_fact.
  assert (Hscan : scan = high_pre) by lia.
  subst scan.
  Exists flat1 rows1 rows1 lens1_2.
  split_pure_spatial.
  - repeat sep_apply store_int_undef_store_int.
    cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try reflexivity.
      first
        [ replace (boundary + 1 - 1) with boundary by lia; exact old_PreH19
        | eapply SwapRowsPrefix_zero__scan_advance; eauto; lia ].
  eapply SwapRowsPrefix_zero__scan_advance; eauto; lia.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_12 : quicksort_numbers_entail_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH30 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre )) by annotation_fact.
  pose proof old_PreH30 as Hwell_formed.
  unfold RowsWellFormed in Hwell_formed.
  destruct Hwell_formed as
    (Hbefore_len & Hlens_len & Hrow_well_formed).
  pose proof (Hrow_well_formed pivot ltac:(lia)) as Hpivot_well_formed.
  pose proof (Hrow_well_formed high_pre ltac:(lia)) as Hhigh_well_formed.
  destruct Hpivot_well_formed as (Hpivot_row_len & _).
  destruct Hhigh_well_formed as (Hhigh_row_len & _).
  pose proof old_PreH34 as Hflat_shape.
  unfold FlatRows in Hflat_shape.
  destruct Hflat_shape as
    (Hflat_len & Hrows_now_len & Hflat_rows).
  pose proof (FlatRows_Znth_cell__pivot_finalization
    flat_now_2 rows_now_2 count_pre number_width_pre
    pivot column old_PreH34 ltac:(lia) ltac:(lia)) as Hpivot_cell.
  pose proof (FlatRows_Znth_cell__pivot_finalization
    flat_now_2 rows_now_2 count_pre number_width_pre
    high_pre column old_PreH34 ltac:(lia) ltac:(lia)) as Hhigh_cell.
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
    Exists flat_now_2 rows_now_2 rows_before_2 lens1_2.
    repeat (split_pure_spatial || split_pures); try cancel;
      dump_pre_spatial; auto; try annotation_fact; try exact Hswap_next; try exact old_PreH34.
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
    Exists flat_after rows_after rows_before_2 lens1_2.
    fold flat_first.
    fold flat_after.
    repeat (split_pure_spatial || split_pures); try cancel;
      dump_pre_spatial; auto; try annotation_fact; try exact Hswap_after; try exact Hflat_after.
Qed.

Lemma proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) by annotation_fact.
  assert (old_PreH18 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH19 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1 ) high_pre )) by annotation_fact.
  assert (old_PreH21 : ((sum (lens1_2)) = (sum (lens)))) by annotation_fact.
  assert (Hcolumn_done : column = number_width_pre) by lia.
  subst column.
  pose proof old_PreH18 as Hwell_formed.
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
    rewrite old_PreH15.
    apply swap_Znth_reverse__pivot_finalization; lia.
  }
  assert (Hwell_formed_after :
    RowsWellFormed rows_now lens_after count_pre number_width_pre).
  {
    rewrite Hrows_swap, Hlens_swap.
    eapply RowsWellFormed_swap__pivot_finalization;
      eauto; lia.
  }
  pose proof old_PreH19 as Hstate_parts.
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
    - exact old_PreH21.
    - rewrite Hlens_before_len. lia.
    - rewrite Hlens_before_len. lia.
  }
  Exists flat_now lens_after rows_now.
  split_pure_spatial.
  - cancel (IntArray.full lengths_pre count_pre lens_after).
    cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat_now).
    apply store_int_undef_store_int.
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hpartitioned_after;
      try exact Hsum_after.
Qed.

Lemma proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH3 : (PairedPermutation rows2 rows1_3 lens2 lens1_3 )) by annotation_fact.
  assert (old_PreH4 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1 ) high_pre )) by annotation_fact.
  assert (old_PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1 ) high_pre )) by annotation_fact.
  assert (old_PreH8 : (RowsWellFormed rows2 lens2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH10 : (PairedPermutation rows1_2 rows2 lens1_2 lens2 )) by annotation_fact.
  assert (old_PreH11 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1 ) )) by annotation_fact.
  assert (old_PreH12 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) by annotation_fact.
  assert (old_PreH26 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH27 : (PairedPermutation rows rows1_2 lens lens1_2 )) by annotation_fact.
  assert (old_PreH28 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) by annotation_fact.
  assert (old_PreH29 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) by annotation_fact.
  Exists lens1_3 flat1_3 rows1_3.
  assert (Hpart2 : GreedyPartitionedAt
        rows2 lens2 low_pre high_pre pivot).
  {
    eapply greedy_partitioned_preserved_left__quicksort_range_composition;
      try exact old_PreH8; try exact old_PreH10; try exact old_PreH11;
      try exact old_PreH29; lia.
  }
  assert (Hpart13 : GreedyPartitionedAt
        rows1_3 lens1_3 low_pre high_pre pivot).
  {
    eapply greedy_partitioned_preserved_right__quicksort_range_composition;
      try exact old_PreH1; try exact old_PreH3; try exact old_PreH4;
      try exact Hpart2; lia.
  }
  assert (Hleft13 : GreedySortedRange
        rows1_3 lens1_3 low_pre (pivot - 1)).
  {
    eapply greedy_sorted_range_preserved_outside__quicksort_range_composition
      with (rows0 := rows2) (lens0 := lens2)
           (change_left := pivot + 1) (change_right := high_pre).
    + exact old_PreH4.
    + lia.
    + destruct old_PreH8 as [Hrows13 _]. rewrite Hrows13. lia.
    + intros k Hk. left. lia.
    + exact old_PreH12.
  }
  assert (Hsum13 : sum lens1_3 = sum lens) by annotation_fact.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact;
      first
        [ eapply greedy_sorted_range_combine__quicksort_range_composition;
          try exact old_PreH1; try exact Hpart13; try exact Hleft13;
          try exact old_PreH5; lia
        | eapply same_outside_paired_range_trans__quicksort_range_composition;
          [ exact old_PreH28
          | eapply same_outside_paired_range_trans__quicksort_range_composition;
            [ eapply same_outside_paired_range_weaken__quicksort_range_composition;
              try exact old_PreH11; lia
            | eapply same_outside_paired_range_weaken__quicksort_range_composition;
              try exact old_PreH4; lia ] ]
        | eapply paired_permutation_trans__quicksort_range_composition;
          [ exact old_PreH27
          | eapply paired_permutation_trans__quicksort_range_composition; eauto ] ].
Qed.

Lemma proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH4 : (PairedPermutation rows1_2 rows2 lens1_2 lens2 )) by annotation_fact.
  assert (old_PreH5 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1 ) )) by annotation_fact.
  assert (old_PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) by annotation_fact.
  assert (old_PreH20 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) by annotation_fact.
  assert (old_PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) by annotation_fact.
  Exists lens2 flat2 rows2.
  assert (Hpart2 : GreedyPartitionedAt
        rows2 lens2 low_pre high_pre pivot).
  {
    eapply (greedy_partitioned_preserved_left__quicksort_range_composition
      rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre
      low_pre high_pre pivot);
      try exact old_PreH2; try exact old_PreH4; try exact old_PreH5;
      try exact old_PreH23; lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact;
      first
        [ eapply greedy_sorted_range_combine__quicksort_range_composition;
          try exact old_PreH2; try exact Hpart2; try exact old_PreH6; try annotation_fact;
          apply greedy_sorted_range_base__quicksort_range_composition; lia
        | eapply same_outside_paired_range_trans__quicksort_range_composition;
          [ exact old_PreH22
          | eapply same_outside_paired_range_weaken__quicksort_range_composition;
            try exact old_PreH5; lia ]
        | eapply paired_permutation_trans__quicksort_range_composition; eauto ].
Qed.

Lemma proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH3 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3 )) by annotation_fact.
  assert (old_PreH4 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1 ) high_pre )) by annotation_fact.
  assert (old_PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1 ) high_pre )) by annotation_fact.
  assert (old_PreH20 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) by annotation_fact.
  assert (old_PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) by annotation_fact.
  Exists lens1_3 flat1_3 rows1_3.
  assert (Hpart3 : GreedyPartitionedAt
        rows1_3 lens1_3 low_pre high_pre pivot).
  {
    eapply (greedy_partitioned_preserved_right__quicksort_range_composition
      rows1_2 rows1_3 lens1_2 lens1_3 count_pre number_width_pre
      low_pre high_pre pivot);
      try exact old_PreH1; try exact old_PreH3; try exact old_PreH4;
      try exact old_PreH23; lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact;
      first
        [ eapply greedy_sorted_range_combine__quicksort_range_composition;
          try exact old_PreH1; try exact Hpart3; try exact old_PreH5; try annotation_fact;
          apply greedy_sorted_range_base__quicksort_range_composition; lia
        | eapply same_outside_paired_range_trans__quicksort_range_composition;
          [ exact old_PreH22
          | eapply same_outside_paired_range_weaken__quicksort_range_composition;
            try exact old_PreH4; lia ]
        | eapply paired_permutation_trans__quicksort_range_composition; eauto ].
Qed.

Lemma proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH13 : (RowsWellFormed rows lens count_pre number_width_pre )) by annotation_fact.
  Exists lens flat rows.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact;
      first
        [ apply greedy_sorted_range_base__quicksort_range_composition; lia
        | apply same_outside_paired_range_refl__quicksort_range_composition
        | apply paired_permutation_refl__quicksort_range_composition;
          destruct old_PreH13 as [Hrows [Hlens _]]; lia ].
Qed.

Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_1 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_2 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_3 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_4 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_5 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_6 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_7 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_8 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_9 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_10 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_11 : quicksort_numbers_partial_solve_wit_23_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1 lens1 count_pre number_width_pre) by annotation_wf.
  match goal with
  | H : PairedPermutation rows1 rows2 lens1 lens2 |- _ =>
    destruct (RowsWellFormed_permutation__annotation _ _ _ _ _ _ Hwf H) as [Hwf2 Hsum2]
  end.
  dump_pre_spatial.
  annotation_fact.
Qed.
Lemma proof_of_quicksort_numbers_partial_solve_wit_23_pure : quicksort_numbers_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_1.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_2.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_3.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_4.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_5.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_6.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_7.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_8.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_9.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_10.
  Goal_apply proof_of_quicksort_numbers_partial_solve_wit_23_pure_split_goal_11.
Qed.
Lemma proof_of_concatenating_numbers_entail_wit_2_1 : concatenating_numbers_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH1 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH5 : (GreedySortedRange rows1_2 lens1_2 0 (count_pre - 1 ) )) by annotation_fact.
  assert (old_PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) by annotation_fact.
  assert (Hsorted : GreedySorted rows1_2 lens1_2).
  {
    unfold GreedySorted.
    intros x y [Hx [Hxy Hy]].
    apply old_PreH5.
    pose proof old_PreH1 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrows_len _].
    rewrite Hrows_len in Hy.
    lia.
  }
  Exists flat1_2 (@nil Z) lens1_2 rows1_2.
  rewrite ConcatenatedPrefix_zero__output_setup.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg result_pre (sum lens)).
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    cancel (IntArray.undef_seg result_pre 0 (sum lens)).
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hsorted.
Qed.

Lemma proof_of_concatenating_numbers_entail_wit_2_2 : concatenating_numbers_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH8 : (RowsWellFormed rows lens count_pre number_width_pre )) by annotation_fact.
  assert (Hcount : count_pre = 1) by lia.
  assert (Hperm : PairedPermutation rows rows lens lens).
  { unfold PairedPermutation.
    pose proof old_PreH8 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrows [Hlens _]].
    repeat split; try lia; apply Permutation_refl. }
  assert (Hsorted : GreedySorted rows lens).
  { unfold GreedySorted.
    intros x y [Hx [Hxy Hy]].
    pose proof old_PreH8 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrows _].
    rewrite Hrows, Hcount in Hy.
    assert (x = 0 /\ y = 0) by lia.
    destruct H as [-> ->].
    unfold item_before_or_equal, digit_lex_ge.
    split; [reflexivity | left; reflexivity]. }
  Exists flat (@nil Z) lens rows.
  rewrite ConcatenatedPrefix_zero__output_setup.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg result_pre (sum lens)).
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat).
    cancel (IntArray.full lengths_pre count_pre lens).
    cancel (IntArray.undef_seg result_pre 0 (sum lens)).
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Hperm; try exact Hsorted.
Qed.

Lemma proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) by annotation_fact.
  assert (Hlens_i : 1 <= Znth i lens1_2 0 <= number_width_pre).
  { pose proof old_PreH10 as Hwf.
    unfold RowsWellFormed in Hwf.
    destruct Hwf as [_ [_ Hrows]].
    specialize (Hrows i ltac:(lia)).
    tauto. }
  assert (Houtput :
      output_2 = ConcatenatedOutputPrefix rows1_2 lens1_2 i 0).
  { rewrite ConcatenatedOutputPrefix_zero__output_setup.
    exact old_PreH14. }
  assert (Hcapacity : result_length < sum lens).
  { pose proof (ConcatenatedOutputPrefix_lt_sum__output_inner_loop
      rows1_2 lens1_2 count_pre number_width_pre i 0
      old_PreH10 ltac:(lia) ltac:(lia)) as Hbound.
    rewrite <- Houtput in Hbound. lia. }
  Exists flat1_2 output_2 rows1_2 lens1_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre (count_pre * number_width_pre) flat1_2).
    cancel (IntArray.full lengths_pre count_pre lens1_2).
    cancel (IntArray.seg result_pre 0 result_length output_2).
    cancel (IntArray.undef_seg result_pre result_length (sum lens)).
  - split_pures; dump_pre_spatial; auto; try annotation_fact; try exact Houtput; try exact Hlens_i.
Qed.

Lemma proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hwf : RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) by annotation_wf.
  assert (Hflat : FlatRows flat1_2 rows1_2 count_pre number_width_pre) by assumption.
  assert (Houtput : output_2 = ConcatenatedOutputPrefix rows1_2 lens1_2 i j) by assumption.
  assert (Hnext : output_2 ++ Znth (i * number_width_pre + j) flat1_2 0 :: nil =
    ConcatenatedOutputPrefix rows1_2 lens1_2 i (j + 1)).
  { rewrite Houtput.
    apply (ConcatenatedOutputPrefix_append__output_inner_loop
      flat1_2 rows1_2 lens1_2 count_pre number_width_pre i j Hflat Hwf); lia. }
  assert (Hnextlen :
    Zlength (output_2 ++ Znth (i * number_width_pre + j) flat1_2 0 :: nil) = result_length + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hcapacity : j + 1 < Znth i lens1_2 0 -> result_length + 1 < sum lens).
  { intros Hj.
    pose proof (ConcatenatedOutputPrefix_lt_sum__output_inner_loop
      rows1_2 lens1_2 count_pre number_width_pre i (j + 1)
      Hwf ltac:(lia) ltac:(lia)) as Hbound.
    rewrite <- Hnext, Hnextlen in Hbound. lia. }
  Exists flat1_2
    (output_2 ++ Znth (i * number_width_pre + j) flat1_2 0 :: nil)
    rows1_2 lens1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact.
Qed.


Lemma proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH14 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH18 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) by annotation_fact.
  Exists flat1_2 output_2 lens1_2 rows1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try annotation_fact.
    assert (Hj : j = Znth i lens1_2 0) by lia.
    rewrite old_PreH18, Hj.
    eapply ConcatenatedOutputPrefix_full_row__output_inner_loop; eauto; lia.
Qed.

Lemma proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (old_PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre )) by annotation_fact.
  assert (old_PreH13 : ((sum (lens1_2)) = (sum (lens)))) by annotation_fact.
  assert (old_PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) by annotation_fact.
  - assert (Hi_eq : i = count_pre) by lia.
    assert (Houtput_eq :
      output_2 = concatenate_rows rows1_2 lens1_2).
    { rewrite old_PreH14, Hi_eq.
      apply ConcatenatedPrefix_full__largest_concatenation_final
        with (width := number_width_pre).
      exact old_PreH10. }
    assert (Houtput_len : Zlength output_2 = sum lens).
    { rewrite Houtput_eq.
      rewrite (RowsWellFormed_concatenate_rows_length__largest_concatenation_final
                 rows1_2 lens1_2 count_pre number_width_pre old_PreH10).
      exact old_PreH13. }
    assert (Hresult_full : result_length = sum lens) by lia.
    assert (Hlargest :
      LargestConcatenation rows lens output_2).
    { rewrite Houtput_eq.
      eapply GreedySorted_LargestConcatenation__largest_concatenation_final;
        eauto. }
    assert (Hwidth : Forall (fun row : list Z => Zlength row = number_width_pre) rows1_2).
    { apply decimal_rows_lengths_from_map. assumption. }
    assert (Hflat : FlatRows flat1 rows1_2 count_pre number_width_pre) by assumption.
    assert (Hdata : flat1 = concat rows1_2).
    { unfold FlatRows in Hflat.
      apply (decimal_rows_concat_unique rows1_2 flat1 count_pre number_width_pre);
        try lia; try tauto; exact Hwidth. }
    Exists lens1_2. Exists rows1_2. Exists output_2.
    split_pure_spatial.
    + rewrite Hresult_full.
      rewrite IntArray.undef_seg_empty.
      sep_apply (IntArray.seg_to_full result_pre 0 (sum lens) output_2).
      replace (result_pre + 0 * sizeof(INT)) with result_pre by lia.
      replace (sum lens - 0) with (sum lens) by lia.
      rewrite Hdata.
      sep_apply (decimal_rows_unflatten rows1_2 numbers_pre count_pre number_width_pre
        ltac:(lia) Hwidth ltac:(lia)).
      repeat cancel; try apply derivable1_refl.
    + split_pures; dump_pre_spatial; auto.
Qed.
