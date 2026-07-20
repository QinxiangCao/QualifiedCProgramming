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
From SimpleC.EE.LLM_bench.Algorithms.energy_necklace Require Import energy_necklace_goal.
From SimpleC.EE.LLM_bench.Algorithms.energy_necklace Require Import energy_necklace_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib.
Local Open Scope sac.

Lemma proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25.
Proof.
  LLM_pre_process (lia || int_auto).
  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       PreH32 PreH29 PreH1 PreH2 (conj PreH7 PreH8) (conj PreH9 PreH10)
       PreH11 (conj PreH12 PreH13) PreH28 PreH30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [Hgain _]]].
  split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27.
Proof.
  LLM_pre_process (lia || int_auto).
  pose proof
    (EnergyValsDuplicated_label_bound__arithmetic_safety_bounds
       beads_l vals_l n_pre left PreH29 PreH31) as Hleft_bound.
  pose proof
    (EnergyValsDuplicated_label_bound__arithmetic_safety_bounds
       beads_l vals_l n_pre (split + 1) PreH29 PreH31) as Hsplit_bound.
  specialize (Hleft_bound ltac:(lia)).
  specialize (Hsplit_bound ltac:(lia)).
  split_pures; dump_pre_spatial; nia.
Qed. 

Lemma proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31.
Proof.
  LLM_pre_process (lia || int_auto).
  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       PreH32 PreH29 PreH1 PreH2 (conj PreH7 PreH8) (conj PreH9 PreH10)
       PreH11 (conj PreH12 PreH13) PreH28 PreH30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [_ [_ Hcandidate]]]].
  split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32.
Proof.
  LLM_pre_process (lia || int_auto).
  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       PreH32 PreH29 PreH1 PreH2 (conj PreH7 PreH8) (conj PreH9 PreH10)
       PreH11 (conj PreH12 PreH13) PreH28 PreH30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [_ [Hsum _]]]].
  split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists (@nil Z).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg vals_pre total).
  rewrite (IntArray.seg_empty vals_pre 0 0).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.undef_seg vals_pre 0 total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
Qed.

Lemma proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists (vals_l_2 ++ Znth i beads_l 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 (i + 1) (vals_l_2 ++ Znth i beads_l 0 :: nil)).
    cancel (IntArray.undef_seg vals_pre (i + 1) total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9; lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
      * rewrite app_Znth1 by lia.
        apply PreH12; lia.
      * assert (k = i) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        rewrite PreH9.
        replace (i - i) with 0 by lia.
        simpl; reflexivity.
Qed.

Lemma proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists vals_l_2.
  split_pure_spatial.
  - rewrite Hi.
    cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 n_pre vals_l_2).
    cancel (IntArray.undef_seg vals_pre n_pre total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    intros k Hk.
    apply PreH12; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2.
  replace (n_pre + 0) with n_pre by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 n_pre vals_l_2).
    cancel (IntArray.undef_seg vals_pre n_pre total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
Qed.

Lemma proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists (vals_l_2 ++ Znth i beads_l 0 :: nil).
  replace (n_pre + (i + 1)) with ((n_pre + i) + 1) by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 ((n_pre + i) + 1)
              (vals_l_2 ++ Znth i beads_l 0 :: nil)).
    cancel (IntArray.undef_seg vals_pre ((n_pre + i) + 1) total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9; lia.
    + intros k Hk.
      rewrite app_Znth1.
      * apply PreH12; lia.
      * rewrite PreH9; lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
      * rewrite app_Znth1.
        -- apply PreH13; lia.
        -- rewrite PreH9; lia.
      * assert (k = i) by lia.
        subst k.
        rewrite app_Znth2.
        -- rewrite PreH9.
           replace (n_pre + i - (n_pre + i)) with 0 by lia.
           simpl; reflexivity.
        -- rewrite PreH9; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists vals_l_2.
  replace (n_pre + n_pre) with total by lia.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full vals_pre 0 total vals_l_2).
  replace (vals_pre + 0 * sizeof ( INT )) with vals_pre by nia.
  replace (total - 0) with total by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    unfold EnergyValsDuplicated.
    repeat split; try lia.
    + intros k Hk.
      apply PreH12; lia.
    + intros k Hk.
      apply PreH13; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 (@nil Z).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg dp_pre (total * width)).
  rewrite (IntArray.seg_empty dp_pre 0 0).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.undef_seg dp_pre 0 (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
Qed.

Lemma proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.seg dp_pre 0 (i + 1) (dp_l_2 ++ 0 :: nil)).
    cancel (IntArray.undef_seg dp_pre (i + 1) (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9; lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
      * rewrite app_Znth1 by lia.
        apply PreH12; lia.
      * assert (k = i) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        rewrite PreH9.
        replace (i - i) with 0 by lia.
        simpl; reflexivity.
Qed.

Lemma proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hi : i = total * width) by lia.
  subst i.
  Exists vals_l_2 dp_l_2.
  rewrite Hi.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full dp_pre 0 (total * width) dp_l_2).
  replace (dp_pre + 0 * sizeof ( INT )) with dp_pre by nia.
  replace (total * width - 0) with (total * width) by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.full dp_pre (total * width) dp_l_2).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + apply EnergyZeroTable_from_prefix__prefix_table_bootstrap with (i := total * width);
        try lia; auto.
      intros k Hk.
      apply PreH12; lia.
    + apply EnergyZeroTable_len_done_2__prefix_table_bootstrap.
      * unfold EnergyValsDuplicated in PreH13.
        destruct PreH13 as [_ [_ [Hvals _]]].
        lia.
      * apply EnergyZeroTable_from_prefix__prefix_table_bootstrap with (i := total * width);
          try lia; auto.
        intros k Hk.
        apply PreH12; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_12 : energyNecklace_entail_wit_12.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  entailer!.
  unfold EnergyLeftProgress, EnergyLenDone in *.
  repeat split; try tauto; try lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  entailer!.
  unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in *.
  repeat split; try tauto; try lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  entailer!.
  all: unfold EnergySplitProgress in PreH19; lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  entailer!.
  all: nia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hdone : EnergyLenDone vals_l dp_l total width len)
    by (unfold EnergySplitProgress, EnergyLeftProgress in PreH30; tauto).
  pose proof PreH32 as Hcomp_bound.
  destruct Hcomp_bound as [_ [Hsplit_bound [_ _]]].
  specialize (Hsplit_bound vals_l dp_l total width len left right split
                PreH29 PreH1 PreH2 ltac:(lia) ltac:(lia) PreH11
                ltac:(lia) PreH28 Hdone).
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hsplit_bound.
  destruct Hsplit_bound as [_ [_ [_ [_ Hcandidate_bound]]]].
  Exists vals_l dp_l.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l).
    cancel (IntArray.full dp_pre (total * width) dp_l).
  - split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_17_2 : energyNecklace_entail_wit_17_2.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hzvals : Zlength vals_l_2 = total)
    by (unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in PreH27; tauto).
  assert (Hcand : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate).
  {
    unfold EnergySplitCandidate, EnergyCellIndex.
    repeat split; try lia.
  }
  pose proof (EnergySplitProgress_step_keep__dp_interval_progress
                vals_l_2 dp_l_2 total width len left right split best candidate
                PreH12 ltac:(lia) PreH27 Hcand PreH22 PreH1) as Hstep.
  Exists vals_l_2 dp_l_2.
  entailer!.
  all: unfold EnergySplitProgress in PreH27; lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_17_1 : energyNecklace_entail_wit_17_1.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hzvals : Zlength vals_l_2 = total)
    by (unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in PreH27; tauto).
  assert (Hcand : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate).
  {
    unfold EnergySplitCandidate, EnergyCellIndex.
    repeat split; try lia.
  }
  pose proof (EnergySplitProgress_step_take__dp_interval_progress
                vals_l_2 dp_l_2 total width len left right split best candidate
                PreH12 ltac:(lia) PreH27 Hcand ltac:(lia) ltac:(lia)) as Hstep.
  Exists vals_l_2 dp_l_2.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hvals_len : Zlength vals_l_2 = total)
    by (unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in PreH24; tauto).
  assert (Hinterval : EnergyIntervalBest vals_l_2 left right best).
  {
    eapply EnergySplitProgress_finish_interval_best__dp_interval_progress.
    - exact PreH12.
    - exact PreH1.
    - rewrite Hvals_len; exact PreH16.
    - exact PreH24.
  }
  assert (Hsplit_right : EnergySplitProgress vals_l_2 dp_l_2 total width len left right best).
  {
    replace right with split by lia.
    exact PreH24.
  }
  Exists vals_l_2 dp_l_2.
  entailer!.
  all: unfold EnergyCellIndex; nia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_20 : energyNecklace_entail_wit_20.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hupdated :
            EnergyUpdatedCell vals_l_2 dp_l
              (replace_Znth ((left * width) + right) best dp_l)
              width left right best).
  {
    unfold EnergyUpdatedCell.
    split.
    - rewrite PreH18.
      unfold EnergyCellIndex; lia.
    - split.
      + unfold EnergyCellIndex; reflexivity.
      + exact PreH21.
  }
  assert (Hleft_progress :
            EnergyLeftProgress vals_l_2
              (replace_Znth ((left * width) + right) best dp_l)
              total width len (left + 1)).
  {
    change (replace_Znth ((left * width) + right) best dp_l) with
      (replace_Znth (EnergyCellIndex width left right) best dp_l).
    apply EnergyLeftProgress_step_update__dp_interval_progress with (right := right);
      try assumption; try lia.
  }
  Exists vals_l_2 (replace_Znth ((left * width) + right) best dp_l) dp_l.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.full dp_pre (total * width)
              (replace_Znth ((left * width) + right) best dp_l)).
  - split_pures; dump_pre_spatial;
      try reflexivity; try assumption; try lia;
      try (rewrite Zlength_replace_Znth; lia).
Qed. 

Lemma proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hdone_next :
            EnergyLenDone vals_l_2 dp_l_2 total width (len + 1)).
  {
    apply EnergyLeftProgress_finish_len__dp_interval_progress with (left := left);
      try assumption; try lia.
  }
  Exists vals_l_2 dp_l_2.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_24 : energyNecklace_entail_wit_24.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  entailer!.
  - unfold EnergyAnswerProgress.
    split; [exact PreH12|].
    split; [exact PreH11|].
    split; [exact PreH3|].
    split; [lia|].
    split; [lia|].
    left; split; lia.
  - replace (n_pre + 1) with len by lia.
    exact PreH13.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_25 : energyNecklace_entail_wit_25.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_answer_bounds__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width 0 answer PreH11) as Hanswer_bounds.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_26 : energyNecklace_entail_wit_26.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyLenDone_rotation_cell_best__answer_loop
    vals_l_2 dp_l_2 total width n_pre start
    PreH4 PreH2 PreH3 ltac:(lia) PreH15) as Hbest.
  unfold EnergyCellIndex in Hbest.
  replace (start * width + (start + n_pre - 1))
    with ((((start * width) + start) + n_pre) - 1) in Hbest by lia.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_27 : energyNecklace_entail_wit_27.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l.
  pose proof (EnergyAnswerCellBounded__answer_loop
    beads_l vals_l_2 dp_l n_pre total width start
    PreH18 PreH13 PreH1 PreH2 ltac:(lia) PreH12 PreH14) as Hbounds.
  unfold EnergyCellIndex in Hbounds.
  replace (start * width + (start + n_pre - 1))
    with ((((start * width) + start) + n_pre) - 1) in Hbounds by lia.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_28_2 : energyNecklace_entail_wit_28_2.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_answer_bounds__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer PreH17) as Hanswer_bounds.
  pose proof (EnergyAnswerProgress_step_keep__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer value
    PreH17 ltac:(lia) PreH18 PreH11 PreH1) as Hprogress_next.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_28_1 : energyNecklace_entail_wit_28_1.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_step_update__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer value
    PreH17 ltac:(lia) PreH18 ltac:(lia) ltac:(lia)) as Hprogress_next.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_30 : energyNecklace_entail_wit_30.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_finish__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer
    PreH4 PreH16 PreH1 PreH9) as Hanswer.
  entailer!.
Qed. 

Lemma proof_of_energyNecklace_return_wit_1 : energyNecklace_return_wit_1.
Proof.
  LLM_pre_process (lia || int_auto).
  subst total.
  subst width.
  Exists dp_l_2 vals_l_2.
  entailer!.
Qed. 
