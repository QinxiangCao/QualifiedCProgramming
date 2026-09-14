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
From SimpleC.EE.LLM_bench.Algorithms.lcs_n Require Import lcs_n_goal.
From SimpleC.EE.LLM_bench.Algorithms.lcs_n Require Import lcs_n_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib.
Local Open Scope sac.

Lemma proof_of_lcs_n_entail_wit_1 : lcs_n_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (repeat (@None Z) (Z.to_nat ((n_pre + 1) * (n_pre + 1))))
         (repeat 0 (Z.to_nat ((n_pre + 1) * (n_pre + 1)))).
  split_pure_spatial.
  - cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full table_pre
        ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1))
      (repeat (@None Z) (Z.to_nat ((n_pre + 1) * (n_pre + 1))))).
  - split_pures; try (dump_pre_spatial; nia).
    dump_pre_spatial.
    apply lcsn_column_progress_zero__column_init_update.
    lia.
Qed.

Lemma proof_of_lcs_n_entail_wit_2_split_goal_1 : lcs_n_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_lcs_n_entail_wit_2 : lcs_n_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcs_n_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_lcs_n_entail_wit_3 : lcs_n_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth (stride * i) (Some 0) mixed_table_2)
         (replace_Znth (stride * i) 0 table_l_2).
  split_pure_spatial.
  - cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1))
      (replace_Znth (stride * i) (Some 0) mixed_table_2)).
  - split_pures; try (dump_pre_spatial; nia).
    dump_pre_spatial.
    eapply lcsn_column_write_progress__column_init_update; eauto; lia.
Qed.

Lemma proof_of_lcs_n_entail_wit_4 : lcs_n_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists mixed_table_2 table_l_2.
  split_pure_spatial.
  - sep_apply_l_atomic (store_int_undef_store_int (&("i")) i).
    cancel (&("i") # Int |->_).
    cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1)) mixed_table_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply lcsn_column_complete_boundary_start__boundary_phase.
    + lia.
    + replace (n_pre + 1) with i by lia.
      assumption.
Qed.

Lemma proof_of_lcs_n_entail_wit_6 : lcs_n_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth j (Some 0) mixed_table_2)
    (replace_Znth j 0 table_l_2).
  split_pure_spatial.
  - cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1))
      (replace_Znth j (Some 0) mixed_table_2)).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply lcsn_boundary_write_progress__boundary_phase.
    + lia.
    + assumption.
Qed.

Lemma proof_of_lcs_n_entail_wit_7 : lcs_n_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists mixed_table_2 table_l_2.
  assert (Hj : j = n_pre + 1) by lia.
  subst j.
  pose proof
    (lcsn_boundaries_complete_rows_start__row_phase_entry
       xs ys mixed_table_2 table_l_2 n_pre PreH9) as Hrows.
  split_pure_spatial.
  - cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1)) mixed_table_2).
    sep_apply (store_int_undef_store_int (&( "j" )) (n_pre + 1)).
    cancel (&( "j" ) # Int |->_).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia; try nia.
Qed.

Lemma proof_of_lcs_n_entail_wit_8 : lcs_n_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists mixed_table_2 table_l_2.
  pose proof
    (lcsn_rows_start_row__row_phase_entry
       xs ys mixed_table_2 table_l_2 n_pre i PreH1 PreH11) as Hrow.
  split_pure_spatial.
  - cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1)) mixed_table_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia; try nia.
Qed.

Lemma proof_of_lcs_n_entail_wit_9_split_goal_1 : lcs_n_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_lcs_n_entail_wit_9_split_goal_2 : lcs_n_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_lcs_n_entail_wit_9_split_goal_3 : lcs_n_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_lcs_n_entail_wit_9 : lcs_n_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcs_n_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_lcs_n_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_lcs_n_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_lcs_n_entail_wit_10_1 : lcs_n_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hprogress :
    LCSNRowProgress xs ys
      (replace_Znth (LCSNCellIndex n_pre i j)
        (Some (Znth (LCSNCellIndex n_pre (i - 1) (j - 1)) table_l_3 0 + 1))
        mixed_table_3)
      (replace_Znth (LCSNCellIndex n_pre i j)
        (Znth (LCSNCellIndex n_pre (i - 1) (j - 1)) table_l_3 0 + 1)
        table_l_3)
      n_pre i (j + 1)).
  {
    eapply lcsn_equal_write_progress__equal_write_and_row_exit;
      try eassumption; lia.
  }
  assert (Hmixed_len :
    Zlength mixed_table_3 = (n_pre + 1) * (n_pre + 1)).
  {
    unfold LCSNRowProgress, LCSNLogicalTableShape in PreH5.
    tauto.
  }
  subst stride.
  rewrite PreH29 in *.
  Exists
    (replace_Znth (LCSNCellIndex n_pre i j)
      (Some (Znth (LCSNCellIndex n_pre (i - 1) (j - 1)) table_l_3 0 + 1))
      mixed_table_3)
    (replace_Znth (LCSNCellIndex n_pre i j)
      (Znth (LCSNCellIndex n_pre (i - 1) (j - 1)) table_l_3 0 + 1)
      table_l_3).
  split_pure_spatial.
  - cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    sep_apply_l_atomic
      (IntArray.seg_single table_pre
        ((n_pre + 1) * (i - 1) + (j - 1))
        (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0)).
    sep_apply_l_atomic
      (IntArray.seg_to_mixed_seg table_pre
        ((n_pre + 1) * (i - 1) + (j - 1))
        ((n_pre + 1) * (i - 1) + (j - 1) + 1)
        (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 :: nil)).
    sep_apply_l_atomic
      (IntArray.mixed_seg_merge_to_mixed_seg table_pre
        0
        ((n_pre + 1) * (i - 1) + (j - 1))
        ((n_pre + 1) * (i - 1) + (j - 1) + 1)
        (sublist 0 ((n_pre + 1) * (i - 1) + (j - 1)) mixed_table_3)
        (map (@Some Z)
          (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 :: nil))).
    + dump_pre_spatial. lia.
    + cbn [map].
      rewrite <- PreH7.
      rewrite <-
        (sublist_single
          None ((n_pre + 1) * (i - 1) + (j - 1)) mixed_table_3) by
        (rewrite Hmixed_len; lia).
      rewrite <-
        (sublist_split
          0
          ((n_pre + 1) * (i - 1) + (j - 1) + 1)
          ((n_pre + 1) * (i - 1) + (j - 1))
          mixed_table_3) by
        (try rewrite Hmixed_len; lia).
      sep_apply_l_atomic
        (IntArray.mixed_seg_merge_to_mixed_seg table_pre
          0
          ((n_pre + 1) * (i - 1) + (j - 1) + 1)
          ((n_pre + 1) * i + j)
          (sublist 0 ((n_pre + 1) * (i - 1) + (j - 1) + 1)
            mixed_table_3)
          (sublist ((n_pre + 1) * (i - 1) + (j - 1) + 1)
            ((n_pre + 1) * i + j) mixed_table_3)).
      { dump_pre_spatial. lia. }
      rewrite <-
        (sublist_split
          0
          ((n_pre + 1) * i + j)
          ((n_pre + 1) * (i - 1) + (j - 1) + 1)
          mixed_table_3) by
        (try rewrite Hmixed_len; lia).
      sep_apply_l_atomic
        (IntArray.seg_single table_pre
          ((n_pre + 1) * i + j)
          (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 + 1)).
      sep_apply_l_atomic
        (IntArray.seg_to_mixed_seg table_pre
          ((n_pre + 1) * i + j)
          ((n_pre + 1) * i + j + 1)
          ((Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 + 1)
            :: nil)).
      sep_apply_l_atomic
        (IntArray.mixed_seg_merge_to_mixed_seg table_pre
          0
          ((n_pre + 1) * i + j)
          ((n_pre + 1) * i + j + 1)
          (sublist 0 ((n_pre + 1) * i + j) mixed_table_3)
          (map (@Some Z)
            ((Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 + 1)
              :: nil))).
      { dump_pre_spatial. lia. }
      cbn [map].
      sep_apply_l_atomic
        (IntArray.mixed_seg_merge_to_mixed_full table_pre
          0
          ((n_pre + 1) * i + j + 1)
          ((n_pre + 1) * (n_pre + 1))
          (sublist 0 ((n_pre + 1) * i + j) mixed_table_3 ++
            Some
              (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 + 1)
              :: nil)
          (sublist ((n_pre + 1) * i + j + 1)
            ((n_pre + 1) * (n_pre + 1)) mixed_table_3)).
      { dump_pre_spatial. lia. }
      rewrite <- app_assoc.
      cbn [List.app].
      rewrite <- Hmixed_len.
      rewrite <-
        (lcsn_replace_Znth_as_sublist__equal_write_and_row_exit
          None mixed_table_3 ((n_pre + 1) * i + j)
          (Some
            (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 + 1))) by
        (rewrite Hmixed_len; lia).
      replace (table_pre + 0 * sizeof(INT)) with table_pre by lia.
      replace (((n_pre + 1) * (n_pre + 1)) - 0)
        with ((n_pre + 1) * (n_pre + 1)) by lia.
      rewrite IntArray.undef_seg_empty.
      replace (Zlength mixed_table_3 - 0) with (Zlength mixed_table_3) by lia.
      unfold LCSNCellIndex.
      replace (i * (n_pre + 1) + j) with ((n_pre + 1) * i + j) by lia.
      replace ((i - 1) * (n_pre + 1) + (j - 1))
        with ((n_pre + 1) * (i - 1) + (j - 1)) by lia.
      cancel
        (IntArray.mixed_full table_pre (Zlength mixed_table_3)
          (replace_Znth ((n_pre + 1) * i + j)
            (Some
              (Znth ((n_pre + 1) * (i - 1) + (j - 1)) table_l_3 0 + 1))
            mixed_table_3)).
      cancel emp.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try lia;
      try nia.
Qed.

Lemma proof_of_lcs_n_entail_wit_10_2 : lcs_n_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst stride.
  rewrite PreH29 in *.
  set (aidx := (n_pre + 1) * (i - 1) + j) in *.
  set (lidx := (n_pre + 1) * i + (j - 1)) in *.
  set (cidx := (n_pre + 1) * i + j) in *.
  set (total := (n_pre + 1) * (n_pre + 1)) in *.
  set (above := Znth aidx table_l_3 0) in *.
  set (left := Znth lidx table_l_3 0) in *.
  assert (Hmax : Z.max above left = above) by (apply Z.max_l; lia).
  assert (Hmixed_len : Zlength mixed_table_3 = total).
  {
    pose proof PreH6 as Hprogress.
    unfold LCSNRowProgress, LCSNLogicalTableShape in Hprogress.
    tauto.
  }
  assert (Hmemory :
    (((((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
         sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil)) ++
       (Some above :: nil)) ++ sublist (cidx + 1) total mixed_table_3) =
    replace_Znth cidx (Some (Z.max above left)) mixed_table_3).
  {
    assert (Hprefix :
      (((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
         sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil)) =
      sublist 0 cidx mixed_table_3).
    {
      rewrite <- PreH8, <- PreH9.
      rewrite <- (sublist_single None aidx mixed_table_3) by
        (rewrite Hmixed_len; unfold aidx, total; nia).
      rewrite <- (sublist_single None lidx mixed_table_3) by
        (rewrite Hmixed_len; unfold lidx, total; nia).
      rewrite <- (sublist_split 0 (aidx + 1) aidx mixed_table_3) by
        (try rewrite Hmixed_len; unfold aidx, total; nia).
      rewrite <- (sublist_split 0 lidx (aidx + 1) mixed_table_3) by
        (try rewrite Hmixed_len; unfold aidx, lidx, total; nia).
      rewrite <- (sublist_split 0 (lidx + 1) lidx mixed_table_3) by
        (try rewrite Hmixed_len; unfold lidx, total; nia).
      replace (lidx + 1) with cidx by (unfold lidx, cidx; lia).
      reflexivity.
    }
    rewrite Hprefix.
    rewrite replace_Znth_sublist__max_write by
      (rewrite Hmixed_len; unfold cidx, total; nia).
    rewrite Hmax, Hmixed_len.
    rewrite <- app_assoc.
    reflexivity.
  }
  Exists (replace_Znth cidx (Some (Z.max above left)) mixed_table_3)
         (replace_Znth cidx (Z.max above left) table_l_3).
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.mixed_seg_single table_pre aidx (Some above)).
    sep_apply_l_atomic
      (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 aidx (aidx + 1)
        (sublist 0 aidx mixed_table_3) (Some above :: nil)).
    + dump_pre_spatial. unfold aidx. nia.
    + sep_apply_l_atomic
        (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 (aidx + 1) lidx
          (sublist 0 aidx mixed_table_3 ++ (Some above :: nil))
          (sublist (aidx + 1) lidx mixed_table_3)).
      * dump_pre_spatial. unfold aidx, lidx. nia.
      * sep_apply_l_atomic (IntArray.mixed_seg_single table_pre lidx (Some left)).
        sep_apply_l_atomic
          (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 lidx (lidx + 1)
            ((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
             sublist (aidx + 1) lidx mixed_table_3) (Some left :: nil)).
        -- dump_pre_spatial. unfold lidx. nia.
        -- replace (lidx + 1) with cidx by (unfold lidx, cidx; lia).
           sep_apply_l_atomic (IntArray.mixed_seg_single table_pre cidx (Some above)).
           sep_apply_l_atomic
             (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 cidx (cidx + 1)
               (((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
                 sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil))
               (Some above :: nil)).
           ++ dump_pre_spatial. unfold cidx. nia.
           ++ sep_apply_l_atomic
                (IntArray.mixed_seg_merge_to_mixed_full table_pre 0 (cidx + 1) total
                  ((((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
                     sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil)) ++
                   (Some above :: nil))
                  (sublist (cidx + 1) total mixed_table_3)).
              ** dump_pre_spatial. unfold cidx, total. nia.
              ** replace (table_pre + 0 * sizeof(INT)) with table_pre by lia.
                 replace (total - 0) with total by lia.
                 rewrite Hmemory.
                 cancel (IntArray.mixed_full table_pre total
                   (replace_Znth cidx (Some (Z.max above left)) mixed_table_3)).
                 cancel (IntArray.full x_pre n_pre xs).
                 cancel (IntArray.full y_pre n_pre ys).
                 sep_apply_l_atomic
                   (store_int_undef_store_int (&( "above")) above).
                 sep_apply_l_atomic
                   (store_int_undef_store_int (&( "left")) left).
                 cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try nia.
    cbv delta [cidx above left aidx lidx].
    replace ((n_pre + 1) * i + j) with (LCSNCellIndex n_pre i j)
      by (unfold LCSNCellIndex; nia).
    replace ((n_pre + 1) * (i - 1) + j)
      with (LCSNCellIndex n_pre (i - 1) j)
      by (unfold LCSNCellIndex; nia).
    replace ((n_pre + 1) * i + (j - 1))
      with (LCSNCellIndex n_pre i (j - 1))
      by (unfold LCSNCellIndex; nia).
    exact (lcsn_max_write_progress__max_write
      xs ys mixed_table_3 table_l_3 n_pre i j
      ltac:(lia) ltac:(lia) PreH6 PreH10).
Qed.

Lemma proof_of_lcs_n_entail_wit_10_3 : lcs_n_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst stride.
  rewrite PreH29 in *.
  set (aidx := (n_pre + 1) * (i - 1) + j) in *.
  set (lidx := (n_pre + 1) * i + (j - 1)) in *.
  set (cidx := (n_pre + 1) * i + j) in *.
  set (total := (n_pre + 1) * (n_pre + 1)) in *.
  set (above := Znth aidx table_l_3 0) in *.
  set (left := Znth lidx table_l_3 0) in *.
  assert (Hmax : Z.max above left = left) by (apply Z.max_r; lia).
  assert (Hmixed_len : Zlength mixed_table_3 = total).
  {
    pose proof PreH6 as Hprogress.
    unfold LCSNRowProgress, LCSNLogicalTableShape in Hprogress.
    tauto.
  }
  assert (Hmemory :
    (((((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
         sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil)) ++
       (Some left :: nil)) ++ sublist (cidx + 1) total mixed_table_3) =
    replace_Znth cidx (Some (Z.max above left)) mixed_table_3).
  {
    assert (Hprefix :
      (((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
         sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil)) =
      sublist 0 cidx mixed_table_3).
    {
      rewrite <- PreH8, <- PreH9.
      rewrite <- (sublist_single None aidx mixed_table_3) by
        (rewrite Hmixed_len; unfold aidx, total; nia).
      rewrite <- (sublist_single None lidx mixed_table_3) by
        (rewrite Hmixed_len; unfold lidx, total; nia).
      rewrite <- (sublist_split 0 (aidx + 1) aidx mixed_table_3) by
        (try rewrite Hmixed_len; unfold aidx, total; nia).
      rewrite <- (sublist_split 0 lidx (aidx + 1) mixed_table_3) by
        (try rewrite Hmixed_len; unfold aidx, lidx, total; nia).
      rewrite <- (sublist_split 0 (lidx + 1) lidx mixed_table_3) by
        (try rewrite Hmixed_len; unfold lidx, total; nia).
      replace (lidx + 1) with cidx by (unfold lidx, cidx; lia).
      reflexivity.
    }
    rewrite Hprefix.
    rewrite replace_Znth_sublist__max_write by
      (rewrite Hmixed_len; unfold cidx, total; nia).
    rewrite Hmax, Hmixed_len.
    rewrite <- app_assoc.
    reflexivity.
  }
  Exists (replace_Znth cidx (Some (Z.max above left)) mixed_table_3)
         (replace_Znth cidx (Z.max above left) table_l_3).
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.mixed_seg_single table_pre aidx (Some above)).
    sep_apply_l_atomic
      (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 aidx (aidx + 1)
        (sublist 0 aidx mixed_table_3) (Some above :: nil)).
    + dump_pre_spatial. unfold aidx. nia.
    + sep_apply_l_atomic
        (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 (aidx + 1) lidx
          (sublist 0 aidx mixed_table_3 ++ (Some above :: nil))
          (sublist (aidx + 1) lidx mixed_table_3)).
      * dump_pre_spatial. unfold aidx, lidx. nia.
      * sep_apply_l_atomic (IntArray.mixed_seg_single table_pre lidx (Some left)).
        sep_apply_l_atomic
          (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 lidx (lidx + 1)
            ((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
             sublist (aidx + 1) lidx mixed_table_3) (Some left :: nil)).
        -- dump_pre_spatial. unfold lidx. nia.
        -- replace (lidx + 1) with cidx by (unfold lidx, cidx; lia).
           sep_apply_l_atomic (IntArray.mixed_seg_single table_pre cidx (Some left)).
           sep_apply_l_atomic
             (IntArray.mixed_seg_merge_to_mixed_seg table_pre 0 cidx (cidx + 1)
               (((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
                 sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil))
               (Some left :: nil)).
           ++ dump_pre_spatial. unfold cidx. nia.
           ++ sep_apply_l_atomic
                (IntArray.mixed_seg_merge_to_mixed_full table_pre 0 (cidx + 1) total
                  ((((sublist 0 aidx mixed_table_3 ++ (Some above :: nil)) ++
                     sublist (aidx + 1) lidx mixed_table_3) ++ (Some left :: nil)) ++
                   (Some left :: nil))
                  (sublist (cidx + 1) total mixed_table_3)).
              ** dump_pre_spatial. unfold cidx, total. nia.
              ** replace (table_pre + 0 * sizeof(INT)) with table_pre by lia.
                 replace (total - 0) with total by lia.
                 rewrite Hmemory.
                 cancel (IntArray.mixed_full table_pre total
                   (replace_Znth cidx (Some (Z.max above left)) mixed_table_3)).
                 cancel (IntArray.full x_pre n_pre xs).
                 cancel (IntArray.full y_pre n_pre ys).
                 sep_apply_l_atomic
                   (store_int_undef_store_int (&( "above")) above).
                 sep_apply_l_atomic
                   (store_int_undef_store_int (&( "left")) left).
                 cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try nia.
    cbv delta [cidx above left aidx lidx].
    replace ((n_pre + 1) * i + j) with (LCSNCellIndex n_pre i j)
      by (unfold LCSNCellIndex; nia).
    replace ((n_pre + 1) * (i - 1) + j)
      with (LCSNCellIndex n_pre (i - 1) j)
      by (unfold LCSNCellIndex; nia).
    replace ((n_pre + 1) * i + (j - 1))
      with (LCSNCellIndex n_pre i (j - 1))
      by (unfold LCSNCellIndex; nia).
    exact (lcsn_max_write_progress__max_write
      xs ys mixed_table_3 table_l_3 n_pre i j
      ltac:(lia) ltac:(lia) PreH6 PreH10).
Qed.

Lemma proof_of_lcs_n_entail_wit_12 : lcs_n_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hrows :
    LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre (i + 1)).
  {
    eapply lcsn_row_finish_progress__equal_write_and_row_exit;
      try eassumption; lia.
  }
  Exists mixed_table_2 table_l_2.
  split_pure_spatial.
  - sep_apply store_int_undef_store_int.
    cancel ((( &( "j" ) )) # Int |->_).
    cancel (IntArray.full x_pre n_pre xs).
    cancel (IntArray.full y_pre n_pre ys).
    cancel (IntArray.mixed_full table_pre
      ((n_pre + 1) * (n_pre + 1)) mixed_table_2).
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try lia;
      try nia.
Qed.

Lemma proof_of_lcs_n_entail_wit_13 : lcs_n_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre + 1) by lia.
  subst i.
  pose proof
    (lcsn_completed_rows_result__finalize_and_return_index
      xs ys mixed_table_2 table_l_2 n_pre PreH3 PreH11) as Hresult.
  pose proof
    (lcsn_initialized_mixed_full_to_full__finalize_and_return_index
      xs ys mixed_table_2 table_l_2 n_pre PreH3 PreH11) as Hmixed.
  rewrite Hmixed in PreH11 |- *.
  Exists (map (@Some Z) table_l_2) table_l_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_to_full table_pre
        ((n_pre + 1) * (n_pre + 1)) table_l_2).
    cancel.
    sep_apply_l_atomic
      (store_int_undef_store_int (&( "i" )) (n_pre + 1)).
    cancel ((( &( "i" ) )) # Int |->_).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_lcs_n_entail_wit_14_split_goal_1 : lcs_n_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_lcs_n_entail_wit_14 : lcs_n_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lcs_n_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_lcs_n_which_implies_wit_1 : lcs_n_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (lcsn_diagonal_observation__read_exposure
       xs ys mixed_table_2 table_l_2 n_pre i j
       PreH1 PreH2 PreH3 PreH4 PreH5) as Hobs.
  destruct Hobs as [Hcurrent [Hdiagonal Hdiag_bound]].
  unfold LCSNCellUndefined, LCSNCellInitialized, LCSNCellIndex
    in Hcurrent, Hdiagonal.
  pose proof PreH5 as Hshape.
  unfold LCSNRowProgress, LCSNLogicalTableShape in Hshape.
  destruct Hshape as [[Hmixed_length Htable_length] Hshape_rest].
  set (diag := (n_pre + 1) * (i - 1) + (j - 1)).
  set (current := (n_pre + 1) * i + j).
  set (total := (n_pre + 1) * (n_pre + 1)).
  assert (Hdiag : Znth diag mixed_table_2 None =
                  Some (Znth diag table_l_2 0)).
  { subst diag. replace ((n_pre + 1) * (i - 1)) with
      ((i - 1) * (n_pre + 1)) by nia. exact Hdiagonal. }
  assert (Hcur : Znth current mixed_table_2 None = None).
  { subst current. replace ((n_pre + 1) * i) with
      (i * (n_pre + 1)) by nia. exact Hcurrent. }
  assert (Hlen : Zlength mixed_table_2 = total).
  { subst total. exact Hmixed_length. }
  assert (Hdiag_bound_index :
    0 <= Znth diag table_l_2 0 <= n_pre).
  { unfold LCSNCellIndex in Hdiag_bound.
    unfold diag.
    replace ((n_pre + 1) * (i - 1)) with ((i - 1) * (n_pre + 1)) by nia.
    exact Hdiag_bound. }
  assert (Hdiag_nonneg : 0 <= diag).
  { unfold diag.
    assert (0 <= (n_pre + 1) * (i - 1)) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  assert (Hdiag_before_current : diag + 1 <= current).
  { unfold diag, current. nia. }
  assert (Hcurrent_before_total : current + 1 <= total).
  { unfold current, total.
    assert (0 <= (n_pre + 1) * (n_pre - i)) by
      (apply Z.mul_nonneg_nonneg; lia).
    nia. }
  Exists mixed_table_2 table_l_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_seg table diag total mixed_table_2).
    + dump_pre_spatial. lia.
    +
    sep_apply_l_atomic
      (IntArray.mixed_seg_split_to_mixed_seg table diag (diag + 1) total
         (sublist diag total mixed_table_2));
      [dump_pre_spatial; lia |].
    assert (Hdiag_slice :
      sublist 0 (diag + 1 - diag) (sublist diag total mixed_table_2) =
      Some (Znth diag table_l_2 0) :: nil).
    { rewrite Zsublist_Zsublist by nia.
      replace (0 + diag) with diag by lia.
      replace (diag + 1 - diag + diag) with (diag + 1) by lia.
      rewrite (@sublist_single (option Z) None diag mixed_table_2) by nia.
      rewrite Hdiag. reflexivity. }
    assert (Hafter_diag_slice :
      sublist (diag + 1 - diag) (total - diag)
        (sublist diag total mixed_table_2) =
      sublist (diag + 1) total mixed_table_2).
    { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
    rewrite Hdiag_slice, Hafter_diag_slice.
    rewrite (IntArray.mixed_seg_unfold table diag (diag + 1) nil
               (Some (Znth diag table_l_2 0))).
    simpl IntArray.mixedstoreA.
    rewrite (IntArray.mixed_seg_empty table (diag + 1)).
    Intros_p Hempty_diag.
    sep_apply_l_atomic
      (IntArray.mixed_seg_split_to_mixed_seg table (diag + 1) current total
         (sublist (diag + 1) total mixed_table_2));
      [dump_pre_spatial; lia |].
    assert (Hmiddle_slice :
      sublist 0 (current - (diag + 1))
        (sublist (diag + 1) total mixed_table_2) =
      sublist (diag + 1) current mixed_table_2).
    { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
    assert (Hafter_middle_slice :
      sublist (current - (diag + 1)) (total - (diag + 1))
        (sublist (diag + 1) total mixed_table_2) =
      sublist current total mixed_table_2).
    { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
    rewrite Hmiddle_slice, Hafter_middle_slice.
    assert (Hcurrent_slice :
      sublist current total mixed_table_2 =
      None :: sublist (current + 1) total mixed_table_2).
    { rewrite (sublist_split current total (current + 1) mixed_table_2)
        by nia.
      rewrite (@sublist_single (option Z) None current mixed_table_2) by nia.
      rewrite Hcur. reflexivity. }
    rewrite Hcurrent_slice.
    rewrite (IntArray.mixed_seg_unfold table current total
               (sublist (current + 1) total mixed_table_2) None).
    simpl IntArray.mixedstoreA.
    sep_apply_l_atomic (IntArray.undef_seg_single table current).
    subst diag current total.
    cancel.
    cancel.
    cancel.
    cancel.
    simpl.
    cancel.
  - split_pures; dump_pre_spatial; try nia.
    + exact PreH5.
    + exact Hcur.
    + exact Hdiag.
Qed.

Lemma proof_of_lcs_n_which_implies_wit_2 : lcs_n_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (lcsn_neighbor_observations__read_exposure
       xs ys mixed_table_2 table_l_2 n_pre i j
       PreH1 PreH2 PreH3 PreH4 PreH5) as Hobs.
  destruct Hobs as [Hcurrent [Habove Hleft]].
  unfold LCSNCellUndefined, LCSNCellInitialized, LCSNCellIndex
    in Hcurrent, Habove, Hleft.
  pose proof PreH5 as Hshape.
  unfold LCSNRowProgress, LCSNLogicalTableShape in Hshape.
  destruct Hshape as [[Hmixed_length Htable_length] Hshape_rest].
  set (above := (n_pre + 1) * (i - 1) + j).
  set (left := (n_pre + 1) * i + (j - 1)).
  set (current := (n_pre + 1) * i + j).
  set (total := (n_pre + 1) * (n_pre + 1)).
  assert (Habove_idx : Znth above mixed_table_2 None =
                       Some (Znth above table_l_2 0)).
  { subst above. replace ((n_pre + 1) * (i - 1)) with
      ((i - 1) * (n_pre + 1)) by nia. exact Habove. }
  assert (Hleft_idx : Znth left mixed_table_2 None =
                      Some (Znth left table_l_2 0)).
  { subst left. replace ((n_pre + 1) * i) with
      (i * (n_pre + 1)) by nia. exact Hleft. }
  assert (Hcur : Znth current mixed_table_2 None = None).
  { subst current. replace ((n_pre + 1) * i) with
      (i * (n_pre + 1)) by nia. exact Hcurrent. }
  assert (Hlen : Zlength mixed_table_2 = total).
  { subst total. exact Hmixed_length. }
  assert (Habove_nonneg : 0 <= above).
  { unfold above.
    assert (0 <= (n_pre + 1) * (i - 1)) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  assert (Habove_before_left : above + 1 <= left).
  { unfold above, left.
    assert (1 <= n_pre) by lia.
    nia. }
  assert (Hleft_current : left + 1 = current).
  { unfold left, current. lia. }
  assert (Hcurrent_before_total : current + 1 <= total).
  { unfold current, total.
    assert (0 <= (n_pre + 1) * (n_pre - i)) by
      (apply Z.mul_nonneg_nonneg; lia).
    nia. }
  Exists mixed_table_2 table_l_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_seg table above total mixed_table_2).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (IntArray.mixed_seg_split_to_mixed_seg table above (above + 1) total
           (sublist above total mixed_table_2));
        [dump_pre_spatial; lia |].
      assert (Habove_slice :
        sublist 0 (above + 1 - above) (sublist above total mixed_table_2) =
        Some (Znth above table_l_2 0) :: nil).
      { rewrite Zsublist_Zsublist by nia.
        replace (0 + above) with above by lia.
        replace (above + 1 - above + above) with (above + 1) by lia.
        rewrite (@sublist_single (option Z) None above mixed_table_2) by nia.
        rewrite Habove_idx. reflexivity. }
      assert (Hafter_above_slice :
        sublist (above + 1 - above) (total - above)
          (sublist above total mixed_table_2) =
        sublist (above + 1) total mixed_table_2).
      { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
      rewrite Habove_slice, Hafter_above_slice.
      rewrite (IntArray.mixed_seg_unfold table above (above + 1) nil
                 (Some (Znth above table_l_2 0))).
      simpl IntArray.mixedstoreA.
      rewrite (IntArray.mixed_seg_empty table (above + 1)).
      Intros_p Hempty_above.
      sep_apply_l_atomic
        (IntArray.mixed_seg_split_to_mixed_seg table (above + 1) left total
           (sublist (above + 1) total mixed_table_2));
        [dump_pre_spatial; lia |].
      assert (Hmiddle_slice :
        sublist 0 (left - (above + 1))
          (sublist (above + 1) total mixed_table_2) =
        sublist (above + 1) left mixed_table_2).
      { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
      assert (Hafter_middle_slice :
        sublist (left - (above + 1)) (total - (above + 1))
          (sublist (above + 1) total mixed_table_2) =
        sublist left total mixed_table_2).
      { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
      rewrite Hmiddle_slice, Hafter_middle_slice.
      sep_apply_l_atomic
        (IntArray.mixed_seg_split_to_mixed_seg table left (left + 1) total
           (sublist left total mixed_table_2));
        [dump_pre_spatial; lia |].
      assert (Hleft_slice :
        sublist 0 (left + 1 - left) (sublist left total mixed_table_2) =
        Some (Znth left table_l_2 0) :: nil).
      { rewrite Zsublist_Zsublist by nia.
        replace (0 + left) with left by lia.
        replace (left + 1 - left + left) with (left + 1) by lia.
        rewrite (@sublist_single (option Z) None left mixed_table_2) by nia.
        rewrite Hleft_idx. reflexivity. }
      assert (Hafter_left_slice :
        sublist (left + 1 - left) (total - left)
          (sublist left total mixed_table_2) =
        sublist (left + 1) total mixed_table_2).
      { rewrite Zsublist_Zsublist by nia. f_equal; nia. }
      rewrite Hleft_slice, Hafter_left_slice.
      rewrite (IntArray.mixed_seg_unfold table left (left + 1) nil
                 (Some (Znth left table_l_2 0))).
      simpl IntArray.mixedstoreA.
      rewrite (IntArray.mixed_seg_empty table (left + 1)).
      Intros_p Hempty_left.
      rewrite Hleft_current.
      assert (Hcurrent_slice :
        sublist current total mixed_table_2 =
        None :: sublist (current + 1) total mixed_table_2).
      { rewrite (sublist_split current total (current + 1) mixed_table_2)
          by nia.
        rewrite (@sublist_single (option Z) None current mixed_table_2) by nia.
        rewrite Hcur. reflexivity. }
      rewrite Hcurrent_slice.
      rewrite (IntArray.mixed_seg_unfold table current total
                 (sublist (current + 1) total mixed_table_2) None).
      simpl IntArray.mixedstoreA.
      sep_apply_l_atomic (IntArray.undef_seg_single table current).
      subst above left current total.
      cancel.
      cancel.
      cancel.
      cancel.
      simpl.
      cancel.
  - split_pures; dump_pre_spatial; try nia.
    + exact PreH5.
    + exact Hcur.
    + exact Habove_idx.
    + exact Hleft_idx.
Qed.
