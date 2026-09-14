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
From SimpleC.EE.LLM_bench.Algorithms.huffman_encoding Require Import huffman_encoding_goal.
From SimpleC.EE.LLM_bench.Algorithms.huffman_encoding Require Import huffman_encoding_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib.
Local Open Scope sac.

Lemma proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (@nil Z) weights_l.
  split_pure_spatial.
  - rewrite (IntArray.seg_empty work_pre 0 0).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg work_pre n_pre).
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial; lia.
  - split_pures.
    all: dump_pre_spatial; (assumption || reflexivity || lia).
Qed.

Lemma proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct remaining_2 as [| next tail].
  - rewrite app_nil_r in *.
    rewrite Zlength_correct in *.
    subst weights_l.
    exfalso; lia.
  - assert (Hnext: Znth i weights_l 0 = next).
    {
      rewrite PreH6.
      rewrite app_Znth2 by lia.
      replace (i - Zlength copied_2) with 0 by lia.
      reflexivity.
    }
    Exists (copied_2 ++ (Znth i weights_l 0 :: nil)) tail.
    split_pure_spatial.
    + cancel (IntArray.seg work_pre 0 (i + 1)
        (copied_2 ++ (Znth i weights_l 0 :: nil))).
      cancel (IntArray.full weights_pre n_pre weights_l).
      cancel (IntArray.undef_seg work_pre (i + 1) n_pre).
    + split_pures.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; exact PreH4.
      * dump_pre_spatial; exact PreH5.
      * dump_pre_spatial.
        rewrite <- app_assoc.
        simpl.
        rewrite Hnext.
        exact PreH6.
      * dump_pre_spatial.
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        lia.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi: i = n_pre) by lia.
  subst i.
  assert (Hremaining: remaining = nil).
  {
    apply Zlength_nil_inv.
    rewrite PreH6 in PreH4.
    rewrite Zlength_app in PreH4.
    lia.
  }
  subst remaining.
  rewrite app_nil_r in PreH6.
  subst copied.
  Exists weights_l.
  split_pure_spatial.
  - rewrite PreH4.
    rewrite (IntArray.undef_seg_empty work_pre n_pre).
    sep_apply_l_atomic (IntArray.seg_to_full work_pre 0 n_pre weights_l).
    replace (work_pre + 0 * sizeof(INT)) with work_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full work_pre n_pre weights_l).
    cancel (IntArray.full weights_pre n_pre weights_l).
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH5.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      eapply huffman_input_live_bounds__copy_initialization; eauto.
    + dump_pre_spatial.
      rewrite <- PreH4.
      apply huffman_initial_progress__copy_initialization; auto.
      lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_4_split_goal_1 : huffman_cost_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply huffman_min_scan_init__min_scan_updates.
Qed.

Lemma proof_of_huffman_cost_entail_wit_4_split_goal_2 : huffman_cost_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_1_split_goal_1 : huffman_cost_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply huffman_min_scan_take_new__min_scan_updates; eauto.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_2_split_goal_1 : huffman_cost_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply huffman_min_scan_keep_old__min_scan_updates.
  - assumption.
  - unfold Z.ge in *.
    apply Z.nlt_ge.
    intro Hlt.
    match goal with
    | Hcmp : (?a ?= ?b)%Z <> Lt |- False =>
        apply Hcmp; apply Z.compare_lt_iff; exact Hlt
    end.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_split_goal_1 : huffman_cost_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HuffmanProgress in PreH20.
  apply huffman_first_held_after_removal__removals_bounds.
  - lia.
  - lia.
  - unfold HuffmanMinScan in *.
    replace i with active in PreH21 by lia.
    exact PreH21.
  - exact PreH20.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_split_goal_2 : huffman_cost_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply replace_last_live_bounds__removals_bounds; eauto; lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_split_goal_3 : huffman_cost_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH19 first ltac:(lia)).
  lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_split_goal_4 : huffman_cost_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH19 first ltac:(lia)).
  lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_split_goal_5 : huffman_cost_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH7.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8 : huffman_cost_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_split_goal_5.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_1 : huffman_cost_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply huffman_min_scan_init__min_scan_updates.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_2 : huffman_cost_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_huffman_cost_entail_wit_10_1_split_goal_1 : huffman_cost_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply huffman_min_scan_take_new__min_scan_updates; eauto.
Qed.

Lemma proof_of_huffman_cost_entail_wit_10_1 : huffman_cost_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_10_2_split_goal_1 : huffman_cost_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply huffman_min_scan_keep_old__min_scan_updates.
  - assumption.
  - unfold Z.ge in *.
    apply Z.nlt_ge.
    intro Hlt.
    match goal with
    | Hcmp : (?a ?= ?b)%Z <> Lt |- False =>
        apply Hcmp; apply Z.compare_lt_iff; exact Hlt
    end.
Qed.

Lemma proof_of_huffman_cost_entail_wit_10_2 : huffman_cost_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_1 : huffman_cost_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply huffman_pair_ready_after_removal__removals_bounds
    with (n := n_pre) (scanned := i).
  - exact PreH7.
  - lia.
  - lia.
  - lia.
  - exact PreH24.
  - exact PreH25.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_2 : huffman_cost_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec k second) as [Heq | Hneq].
  - subst k.
    rewrite Znth_replace_Znth_Same by lia.
    apply PreH23. lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH23. lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_3 : huffman_cost_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct
    (huffman_residual_charge_bounds__removals_bounds
      weights_l work_l active x second total n_pre)
    as [_ Hcharge].
  - exact PreH6.
  - exact PreH7.
  - lia.
  - exact PreH8.
  - lia.
  - lia.
  - exact PreH19.
  - exact PreH24.
  - exact Hcharge.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_4 : huffman_cost_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct
    (huffman_residual_charge_bounds__removals_bounds
      weights_l work_l active x second total n_pre)
    as [Hpair _].
  - exact PreH6.
  - exact PreH7.
  - lia.
  - exact PreH8.
  - lia.
  - lia.
  - exact PreH19.
  - exact PreH24.
  - exact Hpair.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_5 : huffman_cost_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (PreH23 second) as [_ Hupper]; [lia|].
  exact Hupper.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_6 : huffman_cost_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (PreH23 second) as [Hlower _]; [lia|].
  exact Hlower.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12_split_goal_7 : huffman_cost_entail_wit_12_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH7.
Qed.

Lemma proof_of_huffman_cost_entail_wit_12 : huffman_cost_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_6.
  - Goal_apply proof_of_huffman_cost_entail_wit_12_split_goal_7.
Qed.

Lemma proof_of_huffman_cost_entail_wit_13_split_goal_1 : huffman_cost_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (total + (x + y)) with (total + x + y) by lia.
  apply huffman_progress_after_merge__merge_transition.
  - rewrite PreH4. lia.
  - exact PreH20.
Qed.

Lemma proof_of_huffman_cost_entail_wit_13_split_goal_2 : huffman_cost_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct H as [Hk0 Hklt].
  destruct (Z.eq_dec k active) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH19.
    lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_13_split_goal_3 : huffman_cost_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH4.
Qed.

Lemma proof_of_huffman_cost_entail_wit_13 : huffman_cost_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_huffman_cost_entail_wit_13_split_goal_3.
Qed.

Lemma proof_of_huffman_cost_entail_wit_14_split_goal_1 : huffman_cost_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (active = 1) by lia.
  subst active.
  unfold HuffmanProgress, HuffmanResidualOptimum in PreH12.
  destruct PreH12 as [Hsum _].
  unfold HuffmanScratchFinal.
  rewrite sublist_zero_one__final_result in Hsum by lia.
  simpl in Hsum.
  lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_14_split_goal_2 : huffman_cost_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (active = 1) by lia.
  subst active.
  unfold HuffmanProgress, HuffmanResidualOptimum in PreH12.
  destruct PreH12 as [_ [remaining [Hremaining Hinput]]].
  rewrite sublist_zero_one__final_result in Hremaining by lia.
  pose proof
    (huffman_singleton_optimal_zero__final_result
       (Znth 0 work_l 0) remaining Hremaining) as Hzero.
  subst remaining.
  replace (total + 0) with total in Hinput by lia.
  exact Hinput.
Qed.

Lemma proof_of_huffman_cost_entail_wit_14 : huffman_cost_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_14_split_goal_2.
Qed.
