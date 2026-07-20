Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence Require Import longest_increasing_subsequence_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib.
Local Open Scope sac.

Lemma proof_of_lengthOfLIS_safety_wit_5 : lengthOfLIS_safety_wit_5.
Proof.
  pre_process.
  entailer!.
  - replace (j - 0) with j by lia.
    rewrite app_Znth1 by (rewrite PreH10; lia).
    specialize (PreH11 j ltac:(lia)).
    lia.
  - replace (j - 0) with j by lia.
    rewrite app_Znth1 by (rewrite PreH10; lia).
    specialize (PreH11 j ltac:(lia)).
    lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1 : lengthOfLIS_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  split_pure_spatial.
  - cancel (IntArray.full nums_pre numsSize_pre l).
    sep_apply (IntArray.undef_full_split_to_undef_seg dp_pre 0 numsSize_pre).
    + cancel (IntArray.undef_seg dp_pre 0 numsSize_pre).
      rewrite IntArray.undef_seg_empty.
      rewrite IntArray.seg_empty.
      entailer!.
    + lia.
  - split_pures; dump_pre_spatial; simpl;
      unfold LISOuterState, LISDPState; simpl;
      repeat split; auto; try lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2 : lengthOfLIS_entail_wit_2.
Proof.
  pre_process.
  Exists d_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    unfold LISInnerBest.
    split; [lia |].
    split; [lia |].
    split; [destruct PreH9 as [HD _]; exact HD |].
    unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset,
      LISInnerCandidate.
    exists 1.
    split.
    + split.
      * left; reflexivity.
      * intros b Hb.
        destruct Hb as [Hb | (k & Hk0 & Hki & Hlt & Hlis & Hb)].
        -- lia.
        -- lia.
    + reflexivity.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3 : lengthOfLIS_entail_wit_3.
Proof.
  pre_process.
  Exists 1.
  Exists d_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_4 : lengthOfLIS_entail_wit_4.
Proof.
  pre_process.
  Exists best.
  Exists d.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    all:
      replace (j - 0) with j by lia;
      rewrite app_Znth1 by lia;
      specialize (PreH11 j ltac:(lia));
      lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_3 : lengthOfLIS_entail_wit_5_3.
Proof.
  pre_process.
  Exists best_2.
  Exists d_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply lis_inner_best_step_skip; eauto; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_2 : lengthOfLIS_entail_wit_5_2.
Proof.
  pre_process.
  Exists best_2. Exists d_2. split_pure_spatial.
  - cancel (IntArray.full nums_pre numsSize_pre l).
    cancel (IntArray.seg dp_pre 0 (i + 1) (d_2 ++ best_2 :: nil)).
    cancel (IntArray.undef_seg dp_pre (i + 1) numsSize_pre).
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    apply lis_inner_best_step_take; auto; try lia.
    rewrite <- PreH13.
    replace (i - 0) with i in PreH1 by lia.
    eapply Z.le_trans; [exact PreH1 |].
    rewrite znth_app_singleton_last_Z with (i := i) (xs := d_2); auto.
    lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1 : lengthOfLIS_entail_wit_5_1.
Proof.
  pre_process.
  Exists candidate. Exists d_2. split_pure_spatial.
  - replace (replace_Znth i candidate (d_2 ++ best_2 :: nil))
      with (d_2 ++ candidate :: nil).
    + entailer!.
    + rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (i - Zlength d_2) with 0 by lia.
      reflexivity.
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    assert (Hbest_old :
      Znth (i - 0) (d_2 ++ best_2 :: nil) 0 = best_2).
    {
      replace (i - 0) with i by lia.
      rewrite app_Znth2 by lia.
      replace (i - Zlength d_2) with 0 by lia.
      reflexivity.
    }
    assert (Hcand_gt_best : candidate > best_2) by
      (rewrite Hbest_old in PreH1; lia).
    unfold LISInnerBest in *.
    destruct PreH18 as [Hi [Hj [HD Hmax]]].
    split; [lia |].
    split; [lia |].
    split; [exact HD |].
    unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmax as [old [[Hold Hle] Holdval]].
    simpl in Holdval; subst old.
    exists candidate.
    split.
    + split.
      * unfold LISInnerCandidate.
        right.
        exists j.
        repeat split; try lia.
        destruct HD as [_ [_ HDfacts]].
        destruct (HDfacts j ltac:(lia)) as [Hlis _].
        exact Hlis.
      * intros b Hb.
        unfold LISInnerCandidate in Hb.
        destruct Hb as [Hb | Hb].
        -- subst b; lia.
        -- destruct Hb as [k [Hk0j1 [Hki [Hlt [Hlis Hbval]]]]].
           assert (Hkcase : k < j \/ k = j) by lia.
           destruct Hkcase as [Hklt | Hkeq].
           ++ assert (Hprev : LISInnerCandidate l d_2 i j b).
              {
                unfold LISInnerCandidate.
                right.
                exists k.
                repeat split; try lia; auto.
              }
              specialize (Hle b Hprev).
              lia.
           ++ subst k.
              subst b.
              lia.
    + reflexivity.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_7 : lengthOfLIS_entail_wit_7.
Proof.
  pre_process.
  Exists best_2. Exists d_2. split_pure_spatial.
  - cancel (IntArray.full nums_pre numsSize_pre l).
    cancel (IntArray.seg dp_pre 0 (i + 1) (d_2 ++ best_2 :: nil)).
    cancel (IntArray.undef_seg dp_pre (i + 1) numsSize_pre).
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    replace j with i in * by lia. assumption.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_8_2 : lengthOfLIS_entail_wit_8_2.
Proof.
  pre_process.
  Exists best_2. Exists d_2.
  split_pure_spatial.
  - cancel.
    cancel.
  - entailer!.
    assert (HZnth : Znth (i - 0) (d_2 ++ best_2 :: nil) 0 = best_2).
    { replace (i - 0) with i by lia.
      apply znth_app_singleton_last_Z; exact PreH7. }
    rewrite HZnth in PreH1.
    apply LISOuterState_snoc_keep; auto; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_8_1 : lengthOfLIS_entail_wit_8_1.
Proof.
  pre_process.
  Exists best. Exists d.
  split_pure_spatial.
  - cancel.
    cancel.
  - entailer!.
    assert (HZnth : Znth (i - 0) (d ++ best :: nil) 0 = best).
    { replace (i - 0) with i by lia.
      apply znth_app_singleton_last_Z; exact PreH7. }
    rewrite HZnth in PreH1 |- *.
    apply LISOuterState_snoc_take with (ans := ans); auto; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_9 : lengthOfLIS_entail_wit_9.
Proof.
  pre_process.
  Exists (d_2 ++ best :: nil).
  split_pure_spatial.
  - cancel.
    cancel.
  - entailer!.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hki | Hki].
      * rewrite app_Znth1 by (rewrite PreH6; lia).
        specialize (PreH7 k ltac:(lia)).
        lia.
      * replace k with i by lia.
        rewrite app_Znth2 by (rewrite PreH6; lia).
        rewrite PreH6.
        replace (i - i) with 0 by lia.
        rewrite Znth0_cons.
        lia.
    + rewrite Zlength_app.
      rewrite PreH6.
      cbn.
      lia.
Qed.

Lemma proof_of_lengthOfLIS_return_wit_1 : lengthOfLIS_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = numsSize_pre) by lia.
  subst i.
  rewrite Hi.
  Exists d_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre numsSize_pre l).
    unfold IntArray.full, IntArray.seg, IntArray.undef_seg, store_array.
    cancel (store_array_rec
              (fun (x : addr) (lo a : Z) =>
                 (x + lo * sizeof (INT)) # Int |-> a)
              dp_pre 0 numsSize_pre d_2).
    replace (Z.to_nat (numsSize_pre - numsSize_pre)) with O by lia.
    simpl.
    entailer!.
  - entailer!.
    + unfold LISOuterState in PreH9.
      destruct PreH9 as [Hdp [Hans Hcase]].
      rewrite <- Hi.
      rewrite Z.max_r in Hans by lia.
      lia.
    + unfold LISOuterState in PreH9.
      destruct PreH9 as [Hdp [Hans Hcase]].
      lia.
    + unfold LISOuterState in PreH9.
      destruct PreH9 as [Hdp [Hans Hcase]].
      rewrite <- Hi.
      exact Hdp.
    + unfold LISOuterState in PreH9.
      destruct PreH9 as [Hdp [Hans Hcase]].
      unfold LISLength.
      destruct Hcase as [[Hz Hans1] | [Hpos Hlis]].
      * lia.
      * rewrite PreH4.
        rewrite <- Hi.
        exact Hlis.
Qed.
