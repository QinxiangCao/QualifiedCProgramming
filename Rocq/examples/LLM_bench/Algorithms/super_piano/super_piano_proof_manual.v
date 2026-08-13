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
From SimpleC.EE.LLM_bench.Algorithms.super_piano Require Import super_piano_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib.
Local Open Scope sac.

Lemma proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpref_bound : (-1000) * i <= Znth i pref 0 <= 1000 * i).
  {
    eapply PrefixArrayPrefix_entry_abs_bound; [exact PreH7 | | lia].
    intros idx Hidx.
    apply PreH8.
    lia.
  }
  assert (Hl_bound : -1000 <= Znth i l 0 <= 1000) by (apply PreH8; lia).
  replace (i - 0) with i by lia.
  split_pures.
  all: dump_pre_spatial; lia.
Qed. 

Lemma proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single pre_pre 0 0).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.seg pre_pre 0 1 (0 :: nil)).
    cancel (IntArray.undef_seg pre_pre 1 (n_pre + 1)).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia; try (simpl; reflexivity)).
    unfold PrefixArrayPrefix.
    repeat split; simpl; try lia.
Qed. 

Lemma proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists pref_2.
  split_pure_spatial.
  - replace (0 + 1) with 1 by lia.
    cancel.
    cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia; try (simpl; reflexivity)).
Qed. 

Lemma proof_of_build_prefix_entail_wit_3 : build_prefix_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (app pref_2 (cons (((Znth (i - 0) pref_2 0) + (Znth i l 0))) nil)).
  split_pure_spatial.
  - cancel.
    cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia; try (simpl; reflexivity)).
    match goal with
    | Hpref : PrefixArrayPrefix l pref_2 i |- _ =>
        unfold PrefixArrayPrefix in Hpref |- *;
        destruct Hpref as [Hi_nonneg [Hi_bound [Hpref_len [Hpref_zero Hpref_step]]]]
    end.
    repeat split.
    + lia.
    + lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
    + rewrite app_Znth1 by (rewrite Hpref_len; lia).
      exact Hpref_zero.
    + intros j Hj.
      assert (Hj_cases : j < i \/ j = i) by lia.
      destruct Hj_cases as [Hj_lt | Hj_eq].
      * rewrite app_Znth1 by (rewrite Hpref_len; lia).
        rewrite app_Znth1 by (rewrite Hpref_len; lia).
        apply Hpref_step; lia.
      * subst j.
        rewrite app_Znth2 by (rewrite Hpref_len; lia).
        rewrite Hpref_len.
        rewrite app_Znth1 by (rewrite Hpref_len; lia).
        replace (i + 1 - (i + 1)) with 0 by lia.
        replace (i - 0) with i by lia.
        simpl.
        reflexivity.
Qed. 

Lemma proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq : i = n_pre) by lia.
  Exists pref.
  subst i.
  split_pure_spatial.
  - rewrite (IntArray.undef_seg_empty pre_pre (n_pre + 1)).
    cancel (IntArray.full arr_pre n_pre l).
    sep_apply (IntArray.seg_to_full pre_pre 0 (n_pre + 1) pref).
    replace (pre_pre + 0 * sizeof(INT)) with pre_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold PrefixSums.
      rewrite PreH4.
      exact PreH7.
    + dump_pre_spatial.
      intros idx Hidx.
      assert (Hbound : (-1000) * idx <= Znth idx pref 0 <= 1000 * idx).
      {
        eapply PrefixArrayPrefix_entry_abs_bound; [exact PreH7 | exact PreH8 | lia].
      }
      lia.
Qed. 

Lemma proof_of_superPiano_safety_wit_10 : superPiano_safety_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hvalue_int : -2147483648 <= value <= 2147483647).
  {
    match goal with
    | Hvalid : ValidNodeFields ps n_pre L_pre R_pre value start lo hi best |- _ =>
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid;
        destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [_ [Hvalue _]]]]]]]]];
        rewrite Hvalue
    end.
    eapply PrefixSums_diff_int_bounds; eauto; lia.
  }
  pose proof
    (frontier_total_int64_bound
       l ps n_pre L_pre R_pre chosen t total (sublist 0 hsize pop_slots)
       PreH19 PreH18 PreH11 PreH41 PreH29) as Htotal_bound.
  split_pures.
  all: dump_pre_spatial; lia.
Qed. 

Lemma proof_of_superPiano_safety_wit_23 : superPiano_safety_wit_23.
Proof.
  left; LLM_pre_process ltac:(int_auto);
    eapply PrefixSums_diff_int_bounds; eauto; lia.
Qed.

Lemma proof_of_superPiano_safety_wit_39 : superPiano_safety_wit_39.
Proof.
  left; LLM_pre_process ltac:(int_auto);
    eapply PrefixSums_diff_int_bounds; eauto; lia.
Qed.

Lemma proof_of_superPiano_safety_wit_42 : superPiano_safety_wit_42.
Proof.
  left; LLM_pre_process ltac:(int_auto);
    eapply PrefixSums_diff_int_bounds; eauto; lia.
Qed.

Lemma proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hps_eq : ps_3 = ps_2).
  {
    eapply PrefixSums_functional; eauto.
  }
  subst ps_3.
  Exists ans_2; Exists (zeros ((n_pre + 1) * ST_LEVELS)); Exists ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    + rewrite Zlength_correct.
      unfold zeros.
      rewrite repeat_length.
      unfold ST_LEVELS.
      rewrite Z2Nat.id by lia.
      lia.
Qed. 

Lemma proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists vals_2; Exists starts_2; Exists los_2; Exists his_2; Exists bests_2.
  Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists vals_2; Exists starts_2; Exists los_2; Exists his_2; Exists bests_2.
  Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - repeat cancel.
  - unfold InitialFrontierState in PreH19.
    split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (@nil Z); Exists vals_2; Exists starts_2; Exists los_2; Exists his_2.
  Exists bests_2; Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + rewrite PreH11. exact PreH20.
Qed. 

Lemma proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hhsize_pos : 0 < hsize) by (apply PreH38; exact PreH16).
  assert (Hslots_len : hsize <= Zlength slots_2).
  { rewrite PreH29. exact PreH34. }
  pose proof
    (frontier_state_top_node_valid
      ps_2 n_pre L_pre R_pre chosen_2 t total slots_2 hsize
      Hhsize_pos Hslots_len PreH36)
    as Htop_valid.
  assert (
    ValidNodeFields ps_2 n_pre L_pre R_pre
      (heap_top_value slots_2) (heap_top_start slots_2)
      (heap_top_lo slots_2) (heap_top_hi slots_2) (heap_top_best slots_2))
    by exact Htop_valid.
  assert (Hvalid_ret :
    ValidNodeFields ps_2 n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5).
  {
    rewrite PreH10, PreH7, PreH4, PreH1, PreH13.
    exact Htop_valid.
  }
  pose proof Hvalid_ret as Hvalid_ret'.
  unfold ValidNodeFields, ValidNode in Hvalid_ret'; cbn in Hvalid_ret'.
  destruct Hvalid_ret' as
    [_ [Hret_start1 [Hret_startn [Hret_startlo [_ [Hret_hi [Hret_lo_best [Hret_best_hi _]]]]]]]].
  Exists chosen_2; Exists vals_2; Exists starts_2; Exists los_2; Exists his_2.
  Exists bests_2; Exists ans_2; Exists st_slots_2; Exists ps_2; Exists slots_2.
  repeat (split_pure_spatial || split_pures).
  all: try (repeat cancel).
  all: try exact Hslots_len.
  all: try (dump_pre_spatial; try assumption; try lia).
Qed. 

Lemma proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists query_st_slots; Exists query_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    all: try (eapply frontier_pop_to_split_both_children; eauto; lia).
    all: try (eapply valid_node_fields_left_child; eauto; lia).
    all: try (eapply valid_node_fields_right_child; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_8 : superPiano_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists query_st_slots; Exists query_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    all: try (eapply frontier_pop_to_split_left_only; eauto; lia).
    all: try (eapply valid_node_fields_left_child; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_9 : superPiano_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists query_st_slots; Exists query_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    all: try (eapply frontier_pop_to_split_singleton; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_13 : superPiano_entail_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists push_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + match goal with
      | Hpush : FrontierPushFields _ _ _ _ _ _ _ _ |- _ =>
          unfold FrontierPushFields in Hpush;
          eapply frontier_split_push_left_keeps_right_pending; eauto
      end.
Qed. 

Lemma proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists query_st_slots; Exists query_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + eapply frontier_pop_to_split_right_only; eauto; lia.
    + eapply valid_node_fields_right_child; eauto.
Qed.

Lemma proof_of_superPiano_entail_wit_15_4 : superPiano_entail_wit_15_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    rewrite PreH46; lia.
  }
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l push_ps n_pre L_pre R_pre
      left_value start lo (best - 1) left_best); eauto; lia.
  }
  assert (Hstart_lo : start + L_pre - 1 <= lo).
  {
    unfold ValidNodeFields, ValidNode in PreH47; cbn in PreH47.
    lia.
  }
  pose proof PreH47 as Hvalid_fields.
  unfold ValidNodeFields, ValidNode in Hvalid_fields; cbn in Hvalid_fields.
  destruct Hvalid_fields as
    [Hps_len [Hstart_ge [Hstart_le [Hstart_lo_field [Hlo_hi [Hhi_min
      [Hlo_best [Hbest_hi [Hvalue_field Hmax_field]]]]]]]]].
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists push_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + unfold FrontierPushFields in PreH5.
      eapply (frontier_split_push_single_pending_forms_frontier
        push_ps n_pre L_pre R_pre
        (ChordCode n_pre start best :: chosen_2)
        (t + 1) total push_slots hsize
        (mkNode left_value start lo (best - 1) left_best)
        slots_out).
      * exact PreH5.
      * exact PreH27.
Qed.

Lemma proof_of_superPiano_entail_wit_15_3 : superPiano_entail_wit_15_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    rewrite PreH20; lia.
  }
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    rewrite PreH18; lia.
  }
  assert (Hstart_lo : start + L_pre - 1 <= lo).
  {
    unfold ValidNodeFields, ValidNode in PreH34; cbn in PreH34.
    lia.
  }
  pose proof PreH34 as Hvalid_fields.
  unfold ValidNodeFields, ValidNode in Hvalid_fields; cbn in Hvalid_fields.
  destruct Hvalid_fields as
    [Hps_len [Hstart_ge [Hstart_le [Hstart_lo_field [Hlo_hi [Hhi_min
      [Hlo_best [Hbest_hi [Hvalue_field Hmax_field]]]]]]]]].
  Exists chosen_2; Exists vals_2; Exists starts_2; Exists los_2; Exists his_2.
  Exists bests_2; Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_superPiano_entail_wit_15_2 : superPiano_entail_wit_15_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    rewrite PreH21; lia.
  }
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre
      right_value start (best + 1) hi right_best); eauto; lia.
  }
  assert (Hstart_lo : start + L_pre - 1 <= lo).
  {
    unfold ValidNodeFields, ValidNode in PreH45; cbn in PreH45.
    lia.
  }
  pose proof PreH45 as Hvalid_fields.
  unfold ValidNodeFields, ValidNode in Hvalid_fields; cbn in Hvalid_fields.
  destruct Hvalid_fields as
    [Hps_len [Hstart_ge [Hstart_le [Hstart_lo_field [Hlo_hi [Hhi_min
      [Hlo_best [Hbest_hi [Hvalue_field Hmax_field]]]]]]]]].
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists right_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + unfold FrontierPushFields in PreH4.
      eapply (frontier_split_push_single_pending_forms_frontier
        right_ps n_pre L_pre R_pre
        (ChordCode n_pre start best :: chosen_2)
        (t + 1) total right_slots hsize
        (mkNode right_value start (best + 1) hi right_best)
        slots_out).
      * exact PreH4.
      * exact PreH28.
Qed.

Lemma proof_of_superPiano_entail_wit_15_1 : superPiano_entail_wit_15_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH26 as Hsplit_copy.
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre
      right_value start (best + 1) hi right_best); eauto; lia.
  }
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre
      left_value start lo (best - 1) left_best); eauto; lia.
  }
  pose proof PreH51 as Hleft_fields.
  unfold ValidNodeFields, ValidNode in Hleft_fields; cbn in Hleft_fields.
  destruct Hleft_fields as [_ [_ [_ [Hleft_startlo _]]]].
  pose proof PreH52 as Hvalid.
  unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hstartlo [_ [Hhimin _]]]]]].
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists right_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + unfold FrontierPushFields in PreH4.
      eapply (frontier_split_push_single_pending_forms_frontier
        right_ps n_pre L_pre R_pre
        (ChordCode n_pre start best :: chosen_2)
        (t + 1) total right_slots hsize
        (mkNode right_value start (best + 1) hi right_best)
        slots_out).
      * exact PreH4.
      * exact Hsplit_copy.
Qed.

Lemma proof_of_superPiano_entail_wit_16 : superPiano_entail_wit_16.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (ChordCode n_pre start best :: chosen_2).
  Exists vals_2; Exists starts_2; Exists los_2; Exists his_2; Exists bests_2.
  Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + intros Hmore.
      assert (Hcap : hsize <= Zlength slots_2).
      { rewrite PreH13; lia. }
      exact (frontier_state_nonempty_if_more_choices_remain
        ps_2 n_pre L_pre R_pre k_pre ans_2
        (ChordCode n_pre start best :: chosen_2) (t + 1) total slots_2 hsize
        PreH12 PreH32 PreH29 Hcap Hmore).
Qed. 

Lemma proof_of_superPiano_return_wit_1 : superPiano_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists st_slots_2; Exists vals_2; Exists starts_2; Exists los_2; Exists his_2.
  Exists bests_2; Exists slots_2; Exists ps_2.
  split_pure_spatial.
  - replace (n_pre + k_pre + 1) with heap_cap by lia.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    assert (Ht_eq : t = k_pre) by lia.
    subst t.
    eapply frontier_state_complete_implies_answer.
    exact PreH21.
Qed. 

Lemma proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps_2.
  split_pures.
  all: dump_pre_spatial; try assumption; try lia.
  - intros idx Hidx.
    apply PreH10; lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_2_pure : superPiano_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  all: dump_pre_spatial.
  all: unfold PrefixSums, PrefixArrayPrefix in PreH10; lia.
Qed. 

Lemma proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  all: dump_pre_spatial.
  all: unfold PrefixSums, PrefixArrayPrefix in PreH10.
  all: unfold SparseArgmaxBuilt in PreH12.
  all: try assumption; lia.
Qed. 

(* Blocker: these pure witnesses still need real arithmetic/invariant proofs.
   Do not export admitted versions.
Lemma proof_of_superPiano_partial_solve_wit_9_pure : superPiano_partial_solve_wit_9_pure.
Lemma proof_of_superPiano_partial_solve_wit_10_pure : superPiano_partial_solve_wit_10_pure.
Lemma proof_of_superPiano_partial_solve_wit_14_pure : superPiano_partial_solve_wit_14_pure.
*)
