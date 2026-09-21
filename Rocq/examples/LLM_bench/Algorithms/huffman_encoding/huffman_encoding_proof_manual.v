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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib.
Local Open Scope sac.


(* Only the original proved mathematical lemmas are reused. No auto witness is imported. *)
Ltac huffman_prepare :=
  (LLM_pre_process ltac:(lia || int_auto));
  try (match goal with
  | Hl : Forall (Z.le 1) ?w, Hu : Forall (Z.ge 1000) ?w |- _ =>
    assert (Hinput : HuffmanInputBounded w) by
      (apply (proj2 (huffman_input_bounds_iff w)); split; assumption)
  end);
  repeat match goal with
  | H : HuffmanMinScan ?l ?n ?i |- _ =>
      apply (proj1 (huffman_scan_iff l n i ltac:(lia))) in H
  | H : HuffmanFirstHeld ?a ?b ?c ?d ?e |- _ =>
      apply huffman_first_held_iff in H
  | H : HuffmanPairReady ?a ?b ?c ?d ?e ?f |- _ =>
      apply huffman_pair_ready_iff in H
  end;
  try (match goal with
  | Hl : Forall (Z.le 1) (sublist 0 ?n ?l),
    Hu : Forall (Z.ge 8000) (sublist 0 ?n ?l) |- _ =>
    assert (Hlive : forall k, 0 <= k < n -> 1 <= Znth k l 0 <= 8000) by
      (intros k Hk;
       pose proof (proj1 (huffman_prefix_forall_iff _ l n ltac:(lia)) Hl k Hk) as Hlo;
       pose proof (proj1 (huffman_prefix_forall_iff _ l n ltac:(lia)) Hu k Hk) as Hhi;
       apply Z.ge_le in Hhi; lia)
  end).

Ltac huffman_scan_goal :=
  match goal with
  | |- HuffmanMinScan ?l ?n ?i =>
    apply (proj2 (huffman_scan_iff l n i ltac:(lia)))
  end.

 

 

 



 



 



 













 



 



 



 

















 









 








Lemma proof_of_huffman_cost_safety_wit_15_split_goal_1 : huffman_cost_safety_wit_15_split_goal_1.
Proof.
  huffman_prepare. specialize (Hlive second ltac:(lia)).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_huffman_cost_safety_wit_15_split_goal_2 : huffman_cost_safety_wit_15_split_goal_2.
Proof.
  huffman_prepare. specialize (Hlive second ltac:(lia)).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_huffman_cost_safety_wit_15 : huffman_cost_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_huffman_cost_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_huffman_cost_safety_wit_16_split_goal_1 : huffman_cost_safety_wit_16_split_goal_1.
Proof.
  huffman_prepare. specialize (Hlive second ltac:(lia)).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_huffman_cost_safety_wit_16_split_goal_2 : huffman_cost_safety_wit_16_split_goal_2.
Proof.
  huffman_prepare. specialize (Hlive second ltac:(lia)).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_huffman_cost_safety_wit_16 : huffman_cost_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_huffman_cost_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (@nil Z) weights_l.
  split_pure_spatial.
  - rewrite (IntArray.seg_empty (&( "work" )) 0 0).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "work" )) n_pre 8 ltac:(lia)).
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
      rewrite PreH7.
      rewrite app_Znth2 by lia.
      replace (i - Zlength copied_2) with 0 by lia.
      reflexivity.
    }
    Exists (copied_2 ++ (Znth i weights_l 0 :: nil)) tail.
    split_pure_spatial.
    + cancel (IntArray.seg (&( "work" )) 0 (i + 1)
        (copied_2 ++ (Znth i weights_l 0 :: nil))).
      cancel (IntArray.full weights_pre n_pre weights_l).
      cancel (IntArray.undef_seg (&( "work" )) (i + 1) n_pre).
      cancel.
    + split_pures.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; exact PreH4.
      * dump_pre_spatial; exact PreH5.
      * dump_pre_spatial; exact PreH6.
      * dump_pre_spatial.
        rewrite <- app_assoc.
        simpl.
        rewrite Hnext.
        exact PreH7.
      * dump_pre_spatial.
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        lia.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3.
Proof.
  huffman_prepare.
  assert (Hi: i = n_pre) by lia.
  subst i.
  assert (Hremaining: remaining = nil).
  {
    apply Zlength_nil_inv.
    rewrite PreH7 in PreH4.
    rewrite Zlength_app in PreH4.
    lia.
  }
  subst remaining.
  rewrite app_nil_r in PreH7.
  subst copied.
  Exists weights_l.
  split_pure_spatial.
  - rewrite PreH4.
    rewrite (IntArray.undef_seg_empty (&( "work" )) n_pre).
    sep_apply_l_atomic (IntArray.seg_to_full (&( "work" )) 0 n_pre weights_l).
    replace ((&( "work" )) + 0 * sizeof(INT)) with (&( "work" )) by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full (&( "work" )) n_pre weights_l).
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel.
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH5.
    + dump_pre_spatial; exact PreH6.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      apply huffman_prefix_forall_iff; [lia|]. intros k Hk.
      pose proof (huffman_input_live_bounds__copy_initialization weights_l n_pre PreH4 Hinput k Hk). lia.
    + dump_pre_spatial.
      apply huffman_prefix_forall_iff; [lia|]. intros k Hk.
      apply Z.le_ge. pose proof (huffman_input_live_bounds__copy_initialization weights_l n_pre PreH4 Hinput k Hk). lia.
    + dump_pre_spatial.
      rewrite <- PreH4.
      apply huffman_initial_progress__copy_initialization; auto.
      lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_4_split_goal_1 : huffman_cost_entail_wit_4_split_goal_1.
Proof.
  huffman_prepare. huffman_scan_goal.
  apply huffman_min_scan_init__min_scan_updates.
Qed.

Lemma proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_1_split_goal_1 : huffman_cost_entail_wit_6_1_split_goal_1.
Proof.
  huffman_prepare. huffman_scan_goal.
  eapply huffman_min_scan_take_new__min_scan_updates; eauto.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_6_2_split_goal_1 : huffman_cost_entail_wit_6_2_split_goal_1.
Proof.
  huffman_prepare. huffman_scan_goal.
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

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_1 : huffman_cost_entail_wit_7_split_goal_1.
Proof.
  huffman_prepare. huffman_scan_goal.
  apply huffman_min_scan_init__min_scan_updates.
Qed.

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_2 : huffman_cost_entail_wit_7_split_goal_2.
Proof.
  huffman_prepare. apply huffman_first_held_iff.
  eapply huffman_first_held_after_removal__removals_bounds; try lia.
  - replace active with i by lia. assumption.
  - assumption.
Qed.

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_3 : huffman_cost_entail_wit_7_split_goal_3.
Proof.
  huffman_prepare.
  apply huffman_prefix_forall_iff; [rewrite Zlength_replace_Znth; lia|].
  intros k Hk. destruct (Z.eq_dec k first) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    specialize (Hlive (active - 1) ltac:(lia)).
    first [apply Z.le_ge; lia | lia].
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (Hlive k ltac:(lia)).
    first [apply Z.le_ge; lia | lia].
Qed.

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_4 : huffman_cost_entail_wit_7_split_goal_4.
Proof.
  huffman_prepare.
  apply huffman_prefix_forall_iff; [rewrite Zlength_replace_Znth; lia|].
  intros k Hk. destruct (Z.eq_dec k first) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    specialize (Hlive (active - 1) ltac:(lia)).
    first [apply Z.le_ge; lia | lia].
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (Hlive k ltac:(lia)).
    first [apply Z.le_ge; lia | lia].
Qed.

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_5 : huffman_cost_entail_wit_7_split_goal_5.
Proof.
  huffman_prepare. specialize (Hlive first ltac:(lia)). lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_6 : huffman_cost_entail_wit_7_split_goal_6.
Proof.
  huffman_prepare. specialize (Hlive first ltac:(lia)). lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_7_split_goal_7 : huffman_cost_entail_wit_7_split_goal_7.
Proof.
  huffman_prepare. rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_huffman_cost_entail_wit_7 : huffman_cost_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_5.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_6.
  - Goal_apply proof_of_huffman_cost_entail_wit_7_split_goal_7.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_1_split_goal_1 : huffman_cost_entail_wit_8_1_split_goal_1.
Proof.
  huffman_prepare. huffman_scan_goal.
  eapply huffman_min_scan_take_new__min_scan_updates; eauto.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_1 : huffman_cost_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_1_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_8_2_split_goal_1 : huffman_cost_entail_wit_8_2_split_goal_1.
Proof.
  huffman_prepare. huffman_scan_goal.
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

Lemma proof_of_huffman_cost_entail_wit_8_2 : huffman_cost_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_1 : huffman_cost_entail_wit_9_split_goal_1.
Proof.
  huffman_prepare.
  replace (total + (x + Znth second work_l_2 0))
    with (total + x + Znth second work_l_2 0) by lia.
  apply huffman_progress_after_merge__merge_transition.
  - rewrite Zlength_replace_Znth; lia.
  - eapply huffman_pair_ready_after_removal__removals_bounds
      with (n := n_pre) (scanned := i); eauto; lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_2 : huffman_cost_entail_wit_9_split_goal_2.
Proof.
  huffman_prepare.
  pose proof (huffman_residual_charge_bounds__removals_bounds
    weights_l work_l_2 active x second total n_pre
    ltac:(assumption) ltac:(assumption) ltac:(lia) Hinput
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)) as Hb.
  apply huffman_prefix_forall_iff; [repeat rewrite Zlength_replace_Znth; lia|].
  intros k Hk.
  destruct (Z.eq_dec k (active - 1)) as [->|Hlast].
  - rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
    specialize (Hlive second ltac:(lia)).
    first [apply Z.le_ge; lia | lia].
  - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
    destruct (Z.eq_dec k second) as [->|Hsecond].
    + rewrite Znth_replace_Znth_Same by lia.
      specialize (Hlive (active - 1) ltac:(lia)).
      first [apply Z.le_ge; lia | lia].
    + rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hlive k ltac:(lia)). first [apply Z.le_ge; lia | lia].
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_3 : huffman_cost_entail_wit_9_split_goal_3.
Proof.
  huffman_prepare.
  pose proof (huffman_residual_charge_bounds__removals_bounds
    weights_l work_l_2 active x second total n_pre
    ltac:(assumption) ltac:(assumption) ltac:(lia) Hinput
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)) as Hb.
  apply huffman_prefix_forall_iff; [repeat rewrite Zlength_replace_Znth; lia|].
  intros k Hk.
  destruct (Z.eq_dec k (active - 1)) as [->|Hlast].
  - rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
    specialize (Hlive second ltac:(lia)).
    first [apply Z.le_ge; lia | lia].
  - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
    destruct (Z.eq_dec k second) as [->|Hsecond].
    + rewrite Znth_replace_Znth_Same by lia.
      specialize (Hlive (active - 1) ltac:(lia)).
      first [apply Z.le_ge; lia | lia].
    + rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hlive k ltac:(lia)). first [apply Z.le_ge; lia | lia].
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_4 : huffman_cost_entail_wit_9_split_goal_4.
Proof.
  huffman_prepare.
  pose proof (huffman_residual_charge_bounds__removals_bounds
    weights_l work_l_2 active x second total n_pre
    ltac:(assumption) ltac:(assumption) ltac:(lia) Hinput
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_5 : huffman_cost_entail_wit_9_split_goal_5.
Proof.
  huffman_prepare.
  specialize (Hlive second ltac:(lia)). lia.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9_split_goal_6 : huffman_cost_entail_wit_9_split_goal_6.
Proof.
  huffman_prepare.
  repeat rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_4.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_5.
  - Goal_apply proof_of_huffman_cost_entail_wit_9_split_goal_6.
Qed.

Lemma proof_of_huffman_cost_entail_wit_10 : huffman_cost_entail_wit_10.
Proof.
  huffman_prepare.
  assert (active = 1) by lia. subst active.
  assert (Hoptimal : HuffmanOptimalCost weights_l total).
  {
    unfold HuffmanProgress, HuffmanResidualOptimum in PreH14.
    destruct PreH14 as [_ [remaining [Hremaining Hinput_optimal]]].
    rewrite sublist_zero_one__final_result in Hremaining by lia.
    pose proof (huffman_singleton_optimal_zero__final_result
      (Znth 0 work_l 0) remaining Hremaining) as Hzero.
    subst remaining. replace (total + 0) with total in Hinput_optimal by lia.
    exact Hinput_optimal.
  }
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_undef_full (&( "work" )) n_pre work_l).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "work" )) n_pre).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "work" )) 0 n_pre 8 ltac:(lia)).
    simpl. replace ((&( "work" )) + 0) with (&( "work" )) by lia. cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.
