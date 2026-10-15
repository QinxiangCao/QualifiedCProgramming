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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P010_412A_poster_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P010_412A_poster_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P010_412A_poster_lib.
Local Open Scope sac.

Lemma proof_of_write_left_return_wit_1_split_goal_1 : write_left_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ActionSlotBridge.
  split.
  - exact PreH2.
  - exists (76 :: 69 :: 70 :: 84 :: 0 :: nil).
    split.
    + unfold ActionBytes, LeftAction. left. repeat split; reflexivity.
    + destruct (poster_Zlength_8_decompose__write_actions before PreH2)
        as [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 Hbefore]]]]]]]].
      subst before. reflexivity.
Qed.

Lemma proof_of_write_left_return_wit_1_split_goal_2 : write_left_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_replace_Znth.
  exact PreH2.
Qed.

Lemma proof_of_write_left_return_wit_1 : write_left_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_write_left_return_wit_1_split_goal_1.
  - Goal_apply proof_of_write_left_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_write_right_return_wit_1_split_goal_1 : write_right_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ActionSlotBridge.
  split.
  - exact PreH2.
  - exists (82 :: 73 :: 71 :: 72 :: 84 :: 0 :: nil).
    split.
    + unfold ActionBytes, RightAction. right. left. repeat split; reflexivity.
    + destruct (poster_Zlength_8_decompose__write_actions before PreH2)
        as [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 Hbefore]]]]]]]].
      subst before. reflexivity.
Qed.

Lemma proof_of_write_right_return_wit_1_split_goal_2 : write_right_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_replace_Znth.
  exact PreH2.
Qed.

Lemma proof_of_write_right_return_wit_1 : write_right_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_write_right_return_wit_1_split_goal_1.
  - Goal_apply proof_of_write_right_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_write_print_return_wit_1_split_goal_1 : write_print_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ActionSlotBridge.
  split.
  - exact PreH2.
  - exists (80 :: 82 :: 73 :: 78 :: 84 :: 32 :: ch_pre :: 0 :: nil).
    split.
    + unfold ActionBytes, PrintAction. right. right. repeat split; reflexivity.
    + destruct (poster_Zlength_8_decompose__write_actions before PreH2)
        as [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 Hbefore]]]]]]]].
      subst before. reflexivity.
Qed.

Lemma proof_of_write_print_return_wit_1_split_goal_2 : write_print_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_replace_Znth.
  exact PreH2.
Qed.

Lemma proof_of_write_print_return_wit_1 : write_print_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_write_print_return_wit_1_split_goal_1.
  - Goal_apply proof_of_write_print_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold SolverOutputBridge, LeftWalkPlan.
  rewrite Z.sub_diag.
  simpl.
  split; [reflexivity |].
  split; [exact PreH9 |].
  split; [exact PreH9 |].
  split.
  - intros i Hi. lia.
  - intros i Hi. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold LeftWalkPlan.
  rewrite Z.sub_diag.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply left_first_spec__trace_count; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists rows_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray2.full_split_to_missing_i out_pre t (3 * n_pre) 8 rows_2).
    + dump_pre_spatial. lia.
    + cancel (CharArray.full s_pre n_pre text).
      cancel (CharArray2.missing_i out_pre t 0 (3 * n_pre) 8 rows_2).
      pose proof PreH17 as Hbridge.
      unfold SolverOutputBridge in Hbridge.
      destruct Hbridge as [_ [_ [Hrowslen _]]].
      rewrite (Znth_indep rows_2 t nil __default__List_Z) by lia.
      change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8
        (Znth t rows_2 __default__List_Z)) with
        (CharArray.full (out_pre + t * 8 * sizeof (CHAR)) 8
          (Znth t rows_2 __default__List_Z)).
      replace (out_pre + t * 8 * sizeof (CHAR))
        with (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
        by (rewrite sizeof_char; lia).
      cancel (CharArray.full
        (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR)) 8
        (Znth t rows_2 __default__List_Z)).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    exact (PreH18 t (conj PreH13 PreH14)).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    pose proof (CharArray2.missing_i_merge_to_full
      out_pre t (3 * n_pre) 8 rows_2 after) as Hmerge.
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8 after)
      with (CharArray.full (out_pre + t * 8 * sizeof (CHAR)) 8 after) in Hmerge.
    replace (out_pre + t * 8 * sizeof (CHAR))
      with (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR)) in Hmerge
      by (rewrite sizeof_char; lia).
    sep_apply Hmerge; try lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + rewrite (left_walk_plan_step__left_walk k_pre p PreH13 PreH14).
      rewrite Zlength_app, Zlength_cons. simpl. lia.
    + rewrite (left_walk_plan_step__left_walk k_pre p PreH13 PreH14).
      pose proof PreH21 as Hbridge.
      unfold SolverOutputBridge in Hbridge.
      destruct Hbridge as [_ [_ [Hrows _]]].
      assert (Hslot : ActionSlotBridge LeftAction
        (Znth t rows_2 (@nil Z)) after).
      { rewrite (Znth_indep rows_2 t (@nil Z) __default__List_Z)
          by (rewrite Hrows; lia).
        exact PreH2. }
      apply solver_output_bridge_left_append__left_walk;
        [exact PreH21 | exact Hslot | exact PreH18].
    + pose proof PreH21 as Hbridge.
      unfold SolverOutputBridge in Hbridge.
      destruct Hbridge as [_ [_ [Hrows _]]].
      intros i Hi.
      destruct (Z.eq_dec i t) as [Hit | Hit].
      * subst i.
        rewrite (Znth_replace_Znth_Same __default__List_Z rows_2 t after)
          by (rewrite Hrows; lia).
        exact PreH1.
      * rewrite (Znth_replace_Znth_Diff __default__List_Z rows_2 t i after)
          by (try rewrite Hrows; lia).
        apply PreH22. exact Hi.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hp : p = 1) by lia.
  subst p.
  unfold ForwardSweepPlan, ZRange.Zrange.
  simpl.
  simpl in PreH17.
  rewrite app_nil_r.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hp : p = 1) by lia.
  subst p.
  unfold ForwardSweepPlan, ZRange.Zrange.
  simpl.
  rewrite app_nil_r.
  exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcap : t + (2 * (n_pre - p) + 1) < 3 * n_pre).
  { apply PreH14. lia. }
  assert (Hrows_len : Zlength rows_2 = 3 * n_pre).
  { unfold SolverOutputBridge in PreH17. tauto. }
  Exists rows_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray2.full_split_to_missing_i out_pre t (3 * n_pre) 8 rows_2).
    + dump_pre_spatial. lia.
    + rewrite (Znth_indep rows_2 t nil __default__List_Z)
        by (rewrite Hrows_len; lia).
      change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t)
        8 (Znth t rows_2 __default__List_Z)) with
        (CharArray.full (out_pre + t * 8 * sizeof (CHAR)) 8
          (Znth t rows_2 __default__List_Z)).
      replace (out_pre + t * 8 * sizeof (CHAR)) with
        (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR)) by
        (rewrite sizeof_char; ring).
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: eauto.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrows_len : Zlength rows_2 = 3 * n_pre).
  { unfold SolverOutputBridge in PreH24. tauto. }
  assert (Hslot : ActionSlotBridge
      (PrintAction (Znth (p - 1) text 0)) (Znth t rows_2 (@nil Z)) after).
  { rewrite (Znth_indep rows_2 t (@nil Z) __default__List_Z)
      by (rewrite Hrows_len; lia).
    exact PreH3. }
  assert (Hbridge_next : SolverOutputBridge (3 * n_pre)
      (LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text p ++
       PrintAction (Znth (p - 1) text 0) :: nil)
      (t + 1) out_before (replace_Znth t after rows_2)).
  { assert (Hbridge_temp : SolverOutputBridge (3 * n_pre)
        ((LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text p) ++
         PrintAction (Znth (p - 1) text 0) :: nil)
        (t + 1) out_before (replace_Znth t after rows_2)).
    { eapply (SolverOutputBridge_append__left_forward (3 * n_pre)
        (LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text p) t out_before rows_2
        (PrintAction (Znth (p - 1) text 0)) after).
      - lia.
      - exact PreH24.
      - exact Hslot. }
    rewrite <- app_assoc in Hbridge_temp.
    exact Hbridge_temp. }
  assert (Hnext_ret : t + 1 = Zlength
      (LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text p ++
       PrintAction (Znth (p - 1) text 0) :: nil)).
  { unfold SolverOutputBridge in Hbridge_next. tauto. }
  assert (Hrows_shape : forall i : Z,
      0 <= i < 3 * n_pre ->
      Zlength (Znth i (replace_Znth t after rows_2) __default__List_Z) = 8).
  { intros i Hi.
    destruct (Z.eq_dec i t) as [-> | Hneq].
    - rewrite (Znth_replace_Znth_Same __default__List_Z rows_2 t after)
        by (rewrite Hrows_len; lia).
      exact PreH2.
    - rewrite (Znth_replace_Znth_Diff __default__List_Z rows_2 t i after)
        by (try rewrite Hrows_len; lia).
      apply PreH25. exact Hi. }
  assert (Hnext_row_len : Zlength
      (Znth (t + 1) (replace_Znth t after rows_2) __default__List_Z) = 8).
  { apply Hrows_shape. lia. }
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - pose proof (CharArray2.missing_i_merge_to_full out_pre t (3 * n_pre)
      8 rows_2 after) as Hmerge.
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t)
      8 after) with (CharArray.full (out_pre + t * 8 * sizeof (CHAR))
        8 after) in Hmerge.
    replace (out_pre + t * 8 * sizeof (CHAR)) with
      (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR)) in Hmerge by
      (rewrite sizeof_char; ring).
    sep_apply Hmerge; try lia.
    sep_apply_l_atomic (CharArray2.full_split_to_missing_i out_pre (t + 1)
      (3 * n_pre) 8 (replace_Znth t after rows_2)).
    + dump_pre_spatial. lia.
    + rewrite (Znth_indep (replace_Znth t after rows_2) (t + 1) nil
        __default__List_Z) by (rewrite Zlength_replace_Znth, Hrows_len; lia).
      change (CharArray2.ElemArray.full
        (CharArray2.row_addr out_pre 8 (t + 1)) 8
        (Znth (t + 1) (replace_Znth t after rows_2) __default__List_Z)) with
        (CharArray.full (out_pre + (t + 1) * 8 * sizeof (CHAR)) 8
          (Znth (t + 1) (replace_Znth t after rows_2) __default__List_Z)).
      replace (out_pre + (t + 1) * 8 * sizeof (CHAR)) with
        (out_pre + (t + 1) * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR)) by
        (rewrite sizeof_char; ring).
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite <- app_assoc; exact Hnext_ret).
    all: try (rewrite <- app_assoc; exact Hbridge_next).
    all: eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrows_len : Zlength rows_2 = 3 * n_pre).
  { match goal with
    | H : SolverOutputBridge _ _ _ _ rows_2 |- _ =>
        unfold SolverOutputBridge in H; tauto
    end. }
  assert (Hslot : ActionSlotBridge RightAction
      (Znth t rows_2 (@nil Z)) after).
  { rewrite (Znth_indep rows_2 t (@nil Z) __default__List_Z)
      by (rewrite Hrows_len; lia).
    exact PreH2. }
  assert (Hbridge_temp : SolverOutputBridge (3 * n_pre)
      (((LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text p) +::
        PrintAction (Znth (p - 1) text 0)) +:: RightAction)
      (t + 1) out_before (replace_Znth t after rows_2)).
  { eapply (SolverOutputBridge_append__left_forward (3 * n_pre)
      ((LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text p) +::
       PrintAction (Znth (p - 1) text 0)) t out_before rows_2
      RightAction after).
    - lia.
    - exact PreH21.
    - exact Hslot. }
  assert (Hbridge_next : SolverOutputBridge (3 * n_pre)
      (LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text (p + 1))
      (t + 1) out_before (replace_Znth t after rows_2)).
  { rewrite (forward_sweep_step__left_forward text p) by lia.
    rewrite <- app_assoc in Hbridge_temp.
    rewrite <- app_assoc in Hbridge_temp.
    exact Hbridge_temp. }
  assert (Hnext_ret : t + 1 = Zlength
      (LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text (p + 1))).
  { unfold SolverOutputBridge in Hbridge_next. tauto. }
  assert (Hrows_shape : forall i : Z,
      0 <= i < 3 * n_pre ->
      Zlength (Znth i (replace_Znth t after rows_2) __default__List_Z) = 8).
  { intros i Hi.
    destruct (Z.eq_dec i t) as [-> | Hneq].
    - rewrite (Znth_replace_Znth_Same __default__List_Z rows_2 t after)
        by (rewrite Hrows_len; lia).
      exact PreH1.
    - rewrite (Znth_replace_Znth_Diff __default__List_Z rows_2 t i after)
        by (try rewrite Hrows_len; lia).
      apply PreH22. exact Hi. }
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - pose proof (CharArray2.missing_i_merge_to_full out_pre t (3 * n_pre)
      8 rows_2 after) as Hmerge.
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t)
      8 after) with (CharArray.full (out_pre + t * 8 * sizeof (CHAR))
        8 after) in Hmerge.
    replace (out_pre + t * 8 * sizeof (CHAR)) with
      (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR)) in Hmerge by
      (rewrite sizeof_char; ring).
    sep_apply Hmerge; try lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try exact Hnext_ret.
    all: try exact Hbridge_next.
    all: eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    replace (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
      with (out_pre + t * 8 * sizeof (CHAR)) by ring.
    change (CharArray.full (out_pre + t * 8 * sizeof (CHAR)) 8 after)
      with (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t)
        8 after).
    sep_apply (CharArray2.missing_i_merge_to_full out_pre t
      (3 * n_pre) 8 rows_2 after); try lia.
    cancel.
  - destruct PreH24 as [Hret [Hbefore [Hafter [Hactions Hsuffix]]]].
    assert (Hkpre : 1 <= k_pre <= Zlength text)
      by (rewrite <- PreH11; lia).
    assert (Hnpre : 1 <= Zlength text <= 100)
      by (rewrite <- PreH11; lia).
    assert (Hp : p = n_pre) by lia.
    subst p.
    assert (Hplan :
      LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text (n_pre + 1) =
      (LeftWalkPlan k_pre 1 ++ ForwardSweepPlan text n_pre) ++
      (PrintAction (Znth (n_pre - 1) text 0) :: nil)).
    { rewrite forward_sweep_terminal_step__left_exit by lia.
      rewrite app_assoc. reflexivity. }
    split_pures.
    all: try (dump_pre_spatial; eauto).
    all: try (dump_pre_spatial; lia).
    all: try lia.
    + rewrite Hplan, Zlength_app, Zlength_cons, Zlength_nil. lia.
    + unfold SolverOutputBridge. rewrite Hplan.
      split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * split.
        -- exact Hbefore.
        -- split.
           ++ rewrite Zlength_replace_Znth. exact Hafter.
           ++ split.
              ** intros j Hj. destruct (Z_lt_dec j t) as [Hjt|Hjt].
                 --- rewrite app_Znth1 by (rewrite <- Hret; lia).
                     rewrite (Znth_replace_Znth_Diff nil rows_2 t j after) by
                       (try rewrite Hafter; lia).
                     apply Hactions. lia.
                 --- assert (Hj_eq : j = t) by lia. subst j.
                     rewrite app_Znth2 by (rewrite <- Hret; lia).
                     replace (t - Zlength (LeftWalkPlan k_pre 1 ++
                       ForwardSweepPlan text n_pre)) with 0 by lia.
                     rewrite Znth0_cons.
                     rewrite Znth_replace_Znth_Same by (rewrite Hafter; lia).
                     rewrite <- (Hsuffix t) by lia.
                     rewrite (Znth_indep rows_2 t __default__List_Z nil) in PreH3
                       by (rewrite Hafter; lia).
                     exact PreH3.
              ** intros q Hq.
                 rewrite (Znth_replace_Znth_Diff nil rows_2 t q after) by
                   (try rewrite Hafter; lia).
                 apply Hsuffix. lia.
    + intros r Hr. destruct (Z.eq_dec r t) as [->|Hneq].
      * rewrite Znth_replace_Znth_Same by (rewrite Hafter; lia).
        exact PreH2.
      * rewrite (Znth_replace_Znth_Diff __default__List_Z rows_2 t r after)
          by (try rewrite Hafter; lia).
        apply PreH25. exact Hr.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SolverOutputBridge, RightWalkPlan.
  rewrite Z.sub_diag.
  simpl.
  repeat split; auto; try lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RightWalkPlan. rewrite Z.sub_diag. simpl. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply right_first_spec__trace_count; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists rows_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray2.full_split_to_missing_i out_pre t (3 * n_pre) 8 rows_2).
    + dump_pre_spatial. lia.
    + pose proof PreH17 as Hbridge.
      unfold SolverOutputBridge in Hbridge.
      destruct Hbridge as [_ [_ [Hrows _]]].
      assert (Htrows : 0 <= t < Zlength rows_2) by (rewrite Hrows; exact Hp).
      rewrite (Znth_indep rows_2 t nil __default__List_Z Htrows).
      unfold CharArray2.row_addr.
      simpl.
      cancel.
      replace (out_pre + t * 8 * 1) with (out_pre + t * 8 + 0) by ring.
      change (CharArray.full (out_pre + t * 8 + 0) 8
        (Znth t rows_2 __default__List_Z) |--
        CharArray.full (out_pre + t * 8 + 0) 8
          (Znth t rows_2 __default__List_Z)).
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: apply PreH18; lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Holdbridge : SolverOutputBridge (3 * n_pre)
    (RightWalkPlan k_pre p) t out_before rows_2) by assumption.
  pose proof Holdbridge as Hbridge_parts.
  unfold SolverOutputBridge in Hbridge_parts.
  destruct Hbridge_parts as [_ [_ [Hrowslen _]]].
  assert (Htrows : 0 <= t < Zlength rows_2) by
    (rewrite Hrowslen; lia).
  assert (Haction : ActionSlotBridge RightAction
    (Znth t rows_2 (nil : list Z)) after).
  { rewrite (Znth_indep rows_2 t (nil : list Z) __default__List_Z Htrows).
    match goal with
    | H : ActionSlotBridge RightAction _ after |- _ => exact H
    end. }
  assert (Hbridge_next :
    SolverOutputBridge (3 * n_pre)
      (RightWalkPlan k_pre p ++ (RightAction :: nil)) (t + 1)
      out_before (replace_Znth t after rows_2)).
  { eapply solver_output_bridge_append__right_walk.
    - exact Holdbridge.
    - lia.
    - exact Haction. }
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    replace (out_pre + t * (sizeof(CHAR) * 8) + 0 * sizeof(CHAR))
      with (out_pre + t * 8 * 1) by (simpl; ring).
    change
      (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8 after **
       CharArray2.missing_i out_pre t 0 (3 * n_pre) 8 rows_2
      |-- CharArray2.full out_pre (3 * n_pre) 8
        (replace_Znth t after rows_2)).
    sep_apply_l_atomic
      (CharArray2.missing_i_merge_to_full out_pre t (3 * n_pre) 8 rows_2 after).
    + dump_pre_spatial. lia.
    + cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    + rewrite right_walk_snoc__right_walk by lia.
      rewrite Zlength_app_cons. lia.
    + rewrite right_walk_snoc__right_walk by lia.
      exact Hbridge_next.
    + intros i Hi.
      destruct (Z.eq_dec i t) as [Hi_eq|Hi_ne].
      * subst i.
        rewrite Znth_replace_Znth_Same by
          (rewrite Hrowslen; lia).
        exact PreH1.
      * rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth__right_walk, ?Hrowslen; lia).
        match goal with
        | H : forall i : Z, 0 <= i < 3 * n_pre ->
              Zlength (Znth i rows_2 __default__List_Z) = 8 |- _ =>
            apply H; exact Hi
        end.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hp : p = n_pre) by lia.
  subst p.
  assert (Hsweep : BackwardSweepPlan text n_pre = (@nil (Z * Z))).
  { rewrite PreH7. apply backward_sweep_at_end__right_completion. }
  rewrite Hsweep.
  rewrite app_nil_r.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hp : p = n_pre) by lia.
  subst p.
  assert (Hsweep : BackwardSweepPlan text n_pre = (@nil (Z * Z))).
  { rewrite PreH7. apply backward_sweep_at_end__right_completion. }
  rewrite Hsweep.
  rewrite app_nil_r.
  exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_4 : solver_entail_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (CharArray2.full_Zlength out_pre (3 * n_pre) 8 rows_2).
  Intros.
  Exists rows_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray2.full_split_to_missing_i out_pre t (3 * n_pre) 8 rows_2).
    + dump_pre_spatial.
      lia.
    + rewrite (Znth_indep rows_2 t nil __default__List_Z) by lia.
      change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8
        (Znth t rows_2 __default__List_Z)) with
        (CharArray.full (out_pre + t * 8 * sizeof (CHAR)) 8
          (Znth t rows_2 __default__List_Z)).
      replace (out_pre + t * 8 * sizeof (CHAR)) with
        (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
        by (rewrite sizeof_char; lia).
      cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    pose proof (CharArray2.missing_i_merge_to_full out_pre t (3 * n_pre) 8 rows_2 after) as Hm.
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8 after)
      with (CharArray.full
        (out_pre + t * 8 * sizeof (CHAR)) 8 after) in Hm.
    replace (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
      with (out_pre + t * 8 * sizeof (CHAR))
      by (rewrite sizeof_char; nia).
    sep_apply Hm; try lia.
    replace (out_pre + (t + 1) * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
      with (out_pre + (t + 1) * 8 * sizeof (CHAR))
      by (rewrite sizeof_char; nia).
    sep_apply (CharArray2.full_split_to_missing_i out_pre (t + 1) (3 * n_pre) 8
      (replace_Znth t after rows_2)); try lia.
    match goal with H : SolverOutputBridge _ _ _ _ _ |- _ =>
      unfold SolverOutputBridge in H;
      destruct H as [_ [_ [Hrows _]]]
    end.
    rewrite (Znth_indep (replace_Znth t after rows_2) (t + 1) nil __default__List_Z)
      by (rewrite Zlength_replace_Znth; lia).
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 (t + 1)) 8
      (Znth (t + 1) (replace_Znth t after rows_2) __default__List_Z))
      with (CharArray.full (out_pre + (t + 1) * 8 * sizeof (CHAR)) 8
        (Znth (t + 1) (replace_Znth t after rows_2) __default__List_Z)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try (rewrite Zlength_app_cons; lia).
    all: lazymatch goal with
    | |- SolverOutputBridge ?capacity (?plan +:: ?action) (?ret + 1)
        ?before (replace_Znth ?ret ?newrow ?rows) =>
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        pose proof Hbridge as Hbridge';
        unfold SolverOutputBridge in Hbridge';
        destruct Hbridge' as [_ [_ [Hrows _]]]
      end;
      match goal with Hslot : ActionSlotBridge _
        (Znth ?slotindex ?slotrows ?slotdefault) _ |- _ =>
        rewrite (Znth_indep slotrows slotindex slotdefault nil) in Hslot
          by (rewrite Hrows; lia)
      end;
      change (SolverOutputBridge capacity (plan ++ action :: nil)
        (ret + 1) before (replace_Znth ret newrow rows));
      apply (poster_solver_output_bridge_snoc__right_sweep
        capacity plan ret before rows action newrow);
      [assumption | lia | lia | assumption]
    | |- forall i : Z, 0 <= i < ?capacity ->
        Zlength (Znth i (replace_Znth ?ret ?newrow ?rows) _) = ?row_length =>
      intros i Hi;
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        unfold SolverOutputBridge in Hbridge;
        destruct Hbridge as [_ [_ [Hrows _]]]
      end;
      destruct (Z.eq_dec i ret) as [Hi_eq | Hi_ne];
      [subst i;
       rewrite Znth_replace_Znth_Same by (rewrite Hrows; lia);
       match goal with Hnew : Zlength _ = _ |- _ => exact Hnew end
      |rewrite Znth_replace_Znth_Diff;
       try (rewrite Hrows; lia); try lia;
       match goal with Hold : forall j : Z, _ ->
         Zlength (Znth j _ _) = _ |- _ => apply Hold; exact Hi end]
    | |- Zlength (Znth (?ret + 1) (replace_Znth ?ret ?newrow ?rows) _) = ?row_length =>
      match goal with Hbridge : SolverOutputBridge ?capacity ?plan ret ?before rows |- _ =>
        unfold SolverOutputBridge in Hbridge;
        destruct Hbridge as [_ [_ [Hrows _]]]
      end;
      rewrite Znth_replace_Znth_Diff;
      try (rewrite Hrows; lia); try lia;
      match goal with Hold : forall j : Z, _ ->
        Zlength (Znth j _ _) = _ |- _ => apply Hold; lia end
    end.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hret0 : t = Zlength
    ((RightWalkPlan k_pre n_pre ++ BackwardSweepPlan text p) ++
      PrintAction (Znth (p - 1) text 0) :: nil)) by assumption.
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    pose proof (CharArray2.missing_i_merge_to_full out_pre t (3 * n_pre) 8 rows_2 after) as Hm.
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8 after)
      with (CharArray.full
        (out_pre + t * 8 * sizeof (CHAR)) 8 after) in Hm.
    replace (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
      with (out_pre + t * 8 * sizeof (CHAR))
      by (rewrite sizeof_char; nia).
    sep_apply Hm; try lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try (rewrite Zlength_app_cons; lia).
    all: lazymatch goal with
    | |- ?ret + 1 = Zlength (?right ++ BackwardSweepPlan ?text (?p - 1)) =>
      assert (Hplan : BackwardSweepPlan text (p - 1) =
        (BackwardSweepPlan text p ++ PrintAction (Znth (p - 1) text 0) :: nil) ++
          LeftAction :: nil)
        by (apply poster_backward_sweep_step__right_sweep; lia);
      rewrite Hplan;
      repeat rewrite Zlength_app;
      repeat rewrite Zlength_cons;
      rewrite Zlength_app_cons in Hret0;
      rewrite Zlength_app in Hret0;
      replace (Zlength nil) with 0 by reflexivity;
      lia
    | |- SolverOutputBridge ?capacity (?right ++ BackwardSweepPlan ?text (?p - 1))
        (?ret + 1) ?before (replace_Znth ?ret ?newrow ?rows) =>
      assert (Hplan : right ++ BackwardSweepPlan text (p - 1) =
        ((right ++ BackwardSweepPlan text p) ++
          PrintAction (Znth (p - 1) text 0) :: nil) ++ LeftAction :: nil)
        by (apply poster_backward_sweep_step_prefixed__right_sweep; lia);
      rewrite Hplan;
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        pose proof Hbridge as Hbridge';
        unfold SolverOutputBridge in Hbridge';
        destruct Hbridge' as [_ [_ [Hrows _]]]
      end;
      match goal with Hslot : ActionSlotBridge _
        (Znth ?slotindex ?slotrows ?slotdefault) _ |- _ =>
        rewrite (Znth_indep slotrows slotindex slotdefault nil) in Hslot
          by (rewrite Hrows; lia)
      end;
      apply (poster_solver_output_bridge_snoc__right_sweep
        capacity ((right ++ BackwardSweepPlan text p) ++
          PrintAction (Znth (p - 1) text 0) :: nil)
        ret before rows LeftAction newrow);
      [assumption | lia | lia | assumption]
    | |- SolverOutputBridge ?capacity (?plan ++ ?action :: nil) (?ret + 1)
        ?before (replace_Znth ?ret ?newrow ?rows) =>
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        pose proof Hbridge as Hbridge';
        unfold SolverOutputBridge in Hbridge';
        destruct Hbridge' as [_ [_ [Hrows _]]]
      end;
      match goal with Hslot : ActionSlotBridge _
        (Znth ?slotindex ?slotrows ?slotdefault) _ |- _ =>
        rewrite (Znth_indep slotrows slotindex slotdefault nil) in Hslot
          by (rewrite Hrows; lia)
      end;
      apply (poster_solver_output_bridge_snoc__right_sweep
        capacity plan ret before rows action newrow);
      [assumption | lia | lia | assumption]
    | |- forall i : Z, 0 <= i < ?capacity ->
        Zlength (Znth i (replace_Znth ?ret ?newrow ?rows) _) = ?row_length =>
      intros i Hi;
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        unfold SolverOutputBridge in Hbridge;
        destruct Hbridge as [_ [_ [Hrows _]]]
      end;
      destruct (Z.eq_dec i ret) as [Hi_eq | Hi_ne];
      [subst i;
       rewrite Znth_replace_Znth_Same by (rewrite Hrows; lia);
       match goal with Hnew : Zlength _ = _ |- _ => exact Hnew end
      |rewrite Znth_replace_Znth_Diff;
       try (rewrite Hrows; lia); try lia;
       match goal with Hold : forall j : Z, _ ->
         Zlength (Znth j _ _) = _ |- _ => apply Hold; exact Hi end]
    end.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (replace_Znth t after rows_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    pose proof (CharArray2.missing_i_merge_to_full out_pre t (3 * n_pre) 8 rows_2 after) as Hm.
    change (CharArray2.ElemArray.full (CharArray2.row_addr out_pre 8 t) 8 after)
      with (CharArray.full
        (out_pre + t * 8 * sizeof (CHAR)) 8 after) in Hm.
    replace (out_pre + t * (sizeof (CHAR) * 8) + 0 * sizeof (CHAR))
      with (out_pre + t * 8 * sizeof (CHAR))
      by (rewrite sizeof_char; nia).
    sep_apply Hm; try lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try (rewrite Zlength_app_cons; lia).
    all: lazymatch goal with
    | |- ?ret + 1 = Zlength (?right ++ BackwardSweepPlan ?text (?p - 1)) =>
      assert (Hp : p = 1) by lia;
      subst p;
      change (ret + 1 = Zlength (right ++ BackwardSweepPlan text 0));
      assert (Htext : 1 <= Zlength text) by
        (rewrite <- PreH11; lia);
      rewrite (poster_backward_sweep_exit_prefixed__right_sweep right text Htext);
      rewrite Zlength_app_cons;
      lia
    | |- SolverOutputBridge ?capacity (?right ++ BackwardSweepPlan ?text (?p - 1))
        (?ret + 1) ?before (replace_Znth ?ret ?newrow ?rows) =>
      assert (Hp : p = 1) by lia;
      subst p;
      change (SolverOutputBridge capacity (right ++ BackwardSweepPlan text 0)
        (ret + 1) before (replace_Znth ret newrow rows));
      assert (Htext : 1 <= Zlength text) by
        (rewrite <- PreH11; lia);
      rewrite (poster_backward_sweep_exit_prefixed__right_sweep right text Htext);
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        pose proof Hbridge as Hbridge';
        unfold SolverOutputBridge in Hbridge';
        destruct Hbridge' as [_ [_ [Hrows _]]]
      end;
      match goal with Hslot : ActionSlotBridge _
        (Znth ?slotindex ?slotrows ?slotdefault) _ |- _ =>
        rewrite (Znth_indep slotrows slotindex slotdefault nil) in Hslot
          by (rewrite Hrows; lia)
      end;
      apply (poster_solver_output_bridge_snoc__right_sweep
        capacity (right ++ BackwardSweepPlan text 1) ret before rows
        (PrintAction (Znth 0 text 0)) newrow);
      [assumption | lia | lia | assumption]
    | |- forall i : Z, 0 <= i < ?capacity ->
        Zlength (Znth i (replace_Znth ?ret ?newrow ?rows) _) = ?row_length =>
      intros i Hi;
      match goal with Hbridge : SolverOutputBridge _ _ _ _ _ |- _ =>
        unfold SolverOutputBridge in Hbridge;
        destruct Hbridge as [_ [_ [Hrows _]]]
      end;
      destruct (Z.eq_dec i ret) as [Hi_eq | Hi_ne];
      [subst i;
       rewrite Znth_replace_Znth_Same by (rewrite Hrows; lia);
       match goal with Hnew : Zlength _ = _ |- _ => exact Hnew end
      |rewrite Znth_replace_Znth_Diff;
       try (rewrite Hrows; lia); try lia;
       match goal with Hold : forall j : Z, _ ->
         Zlength (Znth j _ _) = _ |- _ => apply Hold; exact Hi end]
    end.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hp : p = n_pre + 1) by lia.
  subst p.
  subst cursor.
  subst n_pre.
  Exists rows (LeftFirstPlan k_pre text).
  split_pure_spatial.
  - cancel (CharArray.full s_pre (Zlength text) text).
    cancel (CharArray2.full out_pre (3 * Zlength text) 8 rows).
  - split_pures.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact PreH17.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst n_pre.
  subst cursor.
  assert (Hp : p = 0) by lia.
  subst p.
  Exists rows (RightFirstPlan k_pre text).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. unfold RightFirstPlan. exact PreH17.
Qed.
