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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P046_1243B2_character_swap_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P046_1243B2_character_swap_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof
    (counted_prefix_counter_bound__count_invariants
      source target counts i (Znth i source 0 - 97)
      PreH9 ltac:(lia) ltac:(lia) ltac:(pose proof (PreH5 i ltac:(lia)); lia)
      PreH11) as Hbound.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof
    (counted_prefix_counter_bound__count_invariants
      source target counts i (Znth i source 0 - 97)
      PreH9 ltac:(lia) ltac:(lia) ltac:(pose proof (PreH5 i ltac:(lia)); lia)
      PreH11) as Hbound.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH5 i ltac:(lia)) as Hsource.
  pose proof (PreH6 i ltac:(lia)) as Htarget.
  pose proof
    (counted_prefix_counter_bound__count_invariants
      source target counts i (Znth i target 0 - 97)
      PreH9 ltac:(lia) ltac:(lia) ltac:(lia) PreH11) as Hbound_target.
  pose proof
    (counted_prefix_counter_bound__count_invariants
      source target counts i (Znth i source 0 - 97)
      PreH9 ltac:(lia) ltac:(lia) ltac:(lia) PreH11) as Hbound_source.
  destruct (Z.eq_dec (Znth i source 0 - 97) (Znth i target 0 - 97)).
  - replace (Znth i source 0 - 97) with (Znth i target 0 - 97) in * by lia.
    rewrite Znth_replace_Znth_Same by (rewrite (proj1 PreH11); lia).
    lia.
  - rewrite Znth_replace_Znth_Diff by
      (try rewrite (proj1 PreH11); lia).
    lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH5 i ltac:(lia)) as Hsource.
  pose proof (PreH6 i ltac:(lia)) as Htarget.
  pose proof
    (counted_prefix_counter_bound__count_invariants
      source target counts i (Znth i target 0 - 97)
      PreH9 ltac:(lia) ltac:(lia) ltac:(lia) PreH11) as Hbound_target.
  pose proof
    (counted_prefix_counter_bound__count_invariants
      source target counts i (Znth i source 0 - 97)
      PreH9 ltac:(lia) ltac:(lia) ltac:(lia) PreH11) as Hbound_source.
  destruct (Z.eq_dec (Znth i source 0 - 97) (Znth i target 0 - 97)).
  - replace (Znth i source 0 - 97) with (Znth i target 0 - 97) in * by lia.
    rewrite Znth_replace_Znth_Same by (rewrite (proj1 PreH11); lia).
    lia.
  - rewrite Znth_replace_Znth_Diff by
      (try rewrite (proj1 PreH11); lia).
    lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CountedPrefix.
  split.
  - unfold repeat_Z, Zlength.
    reflexivity.
  - intros c Hc.
    unfold sublist.
    simpl.
    unfold repeat_Z.
    rewrite Znth_repeat.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH4.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply counted_prefix_step__count_invariants.
  - lia.
  - lia.
  - apply PreH5; lia.
  - apply PreH6; lia.
  - exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CountsEvenBefore.
  intros c Hc.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with n_pre in PreH11 by lia.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj2 (combined_parity_from_full_counts__parity_scan
    source target n_pre counts_2 PreH7 PreH8 PreH11) c).
  - lia.
  - exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj1 (combined_parity_from_full_counts__parity_scan
    source target n_pre counts_2 PreH7 PreH8 PreH11)).
  unfold CountsEvenBefore in *.
  intros k Hk.
  apply PreH12.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply counts_even_before_succ__parity_scan.
  - exact PreH9.
  - rewrite (counted_prefix_full_count__parity_scan
      source target n_pre counts_2 c PreH7 PreH8 PreH11) by lia.
    lia.
  - exact PreH12.
  - exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2 (@nil Z) (@nil Z) (@nil (Z * Z)) target source.
  split_pure_spatial.
  - rewrite (IntArray.full_empty oi_pre 0).
    rewrite (IntArray.full_empty oj_pre 0).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg oi_pre (2 * n_pre)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg oj_pre (2 * n_pre)).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Zlength_nil. lia.
    + apply operation_lists_empty__repair_control.
    + apply repair_state_initial__repair_control. assumption.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2 is_2 js_2 ops_2 tt_2 ss_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre ss_2).
    cancel (CharArray.full t_pre n_pre tt_2).
    cancel (IntArray.full oi_pre m is_2).
    cancel (IntArray.undef_seg oi_pre m (2 * n_pre)).
    cancel (IntArray.full oj_pre m js_2).
    cancel (IntArray.undef_seg oj_pre m (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    apply no_value_range_empty__repair_control.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2 is_2 js_2 ops_2 tt_2 ss_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre ss_2).
    cancel (CharArray.full t_pre n_pre tt_2).
    cancel (IntArray.full oi_pre m is_2).
    cancel (IntArray.undef_seg oi_pre m (2 * n_pre)).
    cancel (IntArray.full oj_pre m js_2).
    cancel (IntArray.undef_seg oj_pre m (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply no_value_range_extend__repair_control; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2 is_2 js_2 ops_2 tt_2 ss_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre ss_2).
    cancel (CharArray.full t_pre n_pre tt_2).
    cancel (IntArray.full oi_pre m is_2).
    cancel (IntArray.undef_seg oi_pre m (2 * n_pre)).
    cancel (IntArray.full oj_pre m js_2).
    cancel (IntArray.undef_seg oj_pre m (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + replace n_pre with j by lia. assumption.
    + apply no_value_range_empty__repair_control.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2 is_2 js_2 ops_2 tt_2 ss_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre ss_2).
    cancel (CharArray.full t_pre n_pre tt_2).
    cancel (IntArray.full oi_pre m is_2).
    cancel (IntArray.undef_seg oi_pre m (2 * n_pre)).
    cancel (IntArray.full oj_pre m js_2).
    cancel (IntArray.undef_seg oj_pre m (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply no_value_range_extend__repair_control; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2
    ((is_2 ++ ((j + 1) :: nil)) ++ ((j + 1) :: nil))
    ((js_2 ++ ((j + 1) :: nil)) ++ ((i + 1) :: nil))
    ((ops_2 ++ ((j, j) :: nil)) ++ ((j, i) :: nil))
    (replace_Znth i
      (Znth j (replace_Znth j (Znth j tt_2 0) ss_2) 0)
      (replace_Znth j (Znth j ss_2 0) tt_2))
    (replace_Znth j
      (Znth i (replace_Znth j (Znth j ss_2 0) tt_2) 0)
      (replace_Znth j (Znth j tt_2 0) ss_2)).
  split_pure_spatial.
  - cancel
      (CharArray.full t_pre n_pre
        (replace_Znth i
          (Znth j (replace_Znth j (Znth j tt_2 0) ss_2) 0)
          (replace_Znth j (Znth j ss_2 0) tt_2))).
    cancel
      (CharArray.full s_pre n_pre
        (replace_Znth j
          (Znth i (replace_Znth j (Znth j ss_2 0) tt_2) 0)
          (replace_Znth j (Znth j tt_2 0) ss_2))).
    cancel
      (IntArray.full oi_pre ((m + 1) + 1)
        ((is_2 ++ ((j + 1) :: nil)) ++ ((j + 1) :: nil))).
    cancel (IntArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre)).
    cancel
      (IntArray.full oj_pre ((m + 1) + 1)
        ((js_2 ++ ((j + 1) :: nil)) ++ ((i + 1) :: nil))).
    cancel (IntArray.undef_seg oj_pre ((m + 1) + 1) (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + eapply
        (replace_znth_preserves_char_bounds__repair_transitions
          (replace_Znth j (Znth j tt_2 0) ss_2) j
          (Znth i (replace_Znth j (Znth j ss_2 0) tt_2) 0) n_pre).
      * rewrite Zlength_replace_Znth__repair_transitions.
        unfold RepairState in PreH22.
        destruct PreH22 as [Hs _]. lia.
      * lia.
      * rewrite Znth_replace_Znth_Diff by
          (unfold RepairState in PreH22;
           destruct PreH22 as [_ [Ht _]]; lia).
        apply PreH8. lia.
      * eapply
          (replace_znth_preserves_char_bounds__repair_transitions
            ss_2 j (Znth j tt_2 0) n_pre).
        -- unfold RepairState in PreH22.
           destruct PreH22 as [Hs _]. lia.
        -- lia.
        -- apply PreH8. lia.
        -- exact PreH7.
    + eapply
        (replace_znth_preserves_char_bounds__repair_transitions
          (replace_Znth j (Znth j ss_2 0) tt_2) i
          (Znth j (replace_Znth j (Znth j tt_2 0) ss_2) 0) n_pre).
      * rewrite Zlength_replace_Znth__repair_transitions.
        unfold RepairState in PreH22.
        destruct PreH22 as [_ [Ht _]]. lia.
      * lia.
      * rewrite Znth_replace_Znth_Same by
          (unfold RepairState in PreH22;
           destruct PreH22 as [Hs _]; lia).
        apply PreH8. lia.
      * eapply
          (replace_znth_preserves_char_bounds__repair_transitions
            tt_2 j (Znth j ss_2 0) n_pre).
        -- unfold RepairState in PreH22.
           destruct PreH22 as [_ [Ht _]]. lia.
        -- lia.
        -- apply PreH7. lia.
        -- exact PreH8.
    + rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
    + apply operation_lists_append__repair_transitions.
      apply operation_lists_append__repair_transitions.
      exact PreH21.
    + apply repair_state_two_cross_swaps__repair_transitions; try assumption.
      * unfold RepairState in PreH22.
        destruct PreH22 as [Hs [Ht _]]. lia.
      * unfold RepairState in PreH22.
        destruct PreH22 as [Hs _]. lia.
      * unfold RepairState in PreH22.
        destruct PreH22 as [Hs _]. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2 is_2 js_2 ops_2 tt_2 ss_2.
  split_pure_spatial.
  - cancel (CharArray.full t_pre n_pre tt_2).
    cancel (CharArray.full s_pre n_pre ss_2).
    cancel (IntArray.full oi_pre m is_2).
    cancel (IntArray.undef_seg oi_pre m (2 * n_pre)).
    cancel (IntArray.full oj_pre m js_2).
    cancel (IntArray.undef_seg oj_pre m (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    apply repair_state_advance_equal__repair_transitions; try assumption.
    unfold RepairState in PreH16.
    destruct PreH16 as [Hs _].
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists counts_2
    (is_2 ++ ((j + 1) :: nil)) (js_2 ++ ((i + 1) :: nil))
    (ops_2 ++ ((j, i) :: nil))
    (replace_Znth i (Znth j ss_2 0) tt_2)
    (replace_Znth j (Znth i tt_2 0) ss_2).
  split_pure_spatial.
  - cancel
      (CharArray.full t_pre n_pre
        (replace_Znth i (Znth j ss_2 0) tt_2)).
    cancel
      (CharArray.full s_pre n_pre
        (replace_Znth j (Znth i tt_2 0) ss_2)).
    cancel (IntArray.full oi_pre (m + 1) (is_2 ++ ((j + 1) :: nil))).
    cancel (IntArray.undef_seg oi_pre (m + 1) (2 * n_pre)).
    cancel (IntArray.full oj_pre (m + 1) (js_2 ++ ((i + 1) :: nil))).
    cancel (IntArray.undef_seg oj_pre (m + 1) (2 * n_pre)).
    cancel (IntArray.full (&( "cnt" )) 26 counts_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + eapply
        (replace_znth_preserves_char_bounds__repair_transitions
          ss_2 j (Znth i tt_2 0) n_pre).
      * unfold RepairState in PreH21.
        destruct PreH21 as [Hs _]. lia.
      * lia.
      * apply PreH8. lia.
      * exact PreH7.
    + eapply
        (replace_znth_preserves_char_bounds__repair_transitions
          tt_2 i (Znth j ss_2 0) n_pre).
      * unfold RepairState in PreH21.
        destruct PreH21 as [_ [Ht _]]. lia.
      * lia.
      * apply PreH7. lia.
      * exact PreH8.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + apply operation_lists_append__repair_transitions. exact PreH20.
    + apply repair_state_one_cross_swap__repair_transitions; try assumption.
      * unfold RepairState in PreH21.
        destruct PreH21 as [Hs [Ht _]]. lia.
      * unfold RepairState in PreH21.
        destruct PreH21 as [Hs _]. lia.
      * unfold RepairState in PreH21.
        destruct PreH21 as [Hs _]. lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength source) by lia.
  assert (Hsource_target : Zlength source = Zlength target) by lia.
  assert (Hwork : SwapsWork source target ops_2).
  {
    eapply repair_state_success_swaps_work__final_results; eauto.
  }
  pose proof Hwork as Hwork_bounds.
  unfold SwapsWork in Hwork_bounds.
  destruct Hwork_bounds as (Hwork_bounds & Hwork_trace).
  assert (Hspec : Spec source target (Some ops_2)).
  {
    unfold Spec. right. exists ops_2. auto.
  }
  unfold OperationLists in PreH14.
  destruct PreH14 as (Hislen & Hjslen & Hops_lists).
  assert (Hops_lists_default :
    forall q, 0 <= q < Zlength ops_2 ->
      Znth q is_2 0 = fst (Znth q ops_2 __default__Prod_Z_Z) + 1 /\
      Znth q js_2 0 = snd (Znth q ops_2 __default__Prod_Z_Z) + 1).
  {
    intros q Hq.
    rewrite (Znth_indep ops_2 q __default__Prod_Z_Z (0, 0) Hq).
    apply Hops_lists. exact Hq.
  }
  subst m.
  Exists js_2 is_2 ops_2 (Some ops_2).
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_to_full_shape s_pre n_pre ss).
    sep_apply_l_atomic (CharArray.full_to_full_shape t_pre n_pre tt).
    cancel.
  - split_pures; dump_pre_spatial; try assumption;
      try exact Hops_lists_default;
      try reflexivity; try lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH21 as Hrepair.
  unfold RepairState in Hrepair.
  destruct Hrepair as
    (Hslen & Htlen & Hprefix & Hperm & Heven & Htrace & Hops).
  assert (Hj : j = n_pre) by lia.
  assert (Hlengths : Zlength ss = Zlength tt) by lia.
  assert (Hibounds : 0 <= i < Zlength ss) by lia.
  specialize (PreH6 i ltac:(lia)).
  assert (Hv : 97 <= Znth i ss 0 <= 122) by lia.
  assert (Htuf :
    NoValueInRange tt (Znth i ss 0) (i + 1) (Zlength tt)).
  {
    assert (Hjt : Zlength tt = j) by lia.
    rewrite Hjt. exact PreH16.
  }
  assert (Hsuf :
    NoValueInRange ss (Znth i ss 0) (i + 1) (Zlength ss)).
  {
    assert (Hsn : Zlength ss = n_pre) by lia.
    rewrite Hsn. exact PreH15.
  }
  assert (Hti : Znth i tt 0 <> Znth i ss 0).
  { intro Heq. apply PreH14. symmetry. exact Heq. }
  exfalso.
  exact
    (no_match_contradicts_combined_even__final_results
      ss tt i (Znth i ss 0)
      Hlengths Hibounds Hv Hprefix eq_refl Hti Hsuf Htuf Heven).
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnone : ~ exists ops, SwapsWork source target ops).
  {
    intros (ops & Hwork).
    eapply combined_odd_forbids_swaps_work__final_results; eauto.
  }
  assert (Hspec : Spec source target None).
  {
    unfold Spec. left. auto.
  }
  Exists
    (repeat None (Z.to_nat (2 * n_pre)))
    (repeat None (Z.to_nat (2 * n_pre)))
    None.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.full_to_full_shape s_pre n_pre source).
    sep_apply_l_atomic
      (CharArray.full_to_full_shape t_pre n_pre target).
    sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full oi_pre (2 * n_pre)).
    sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full oj_pre (2 * n_pre)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.
