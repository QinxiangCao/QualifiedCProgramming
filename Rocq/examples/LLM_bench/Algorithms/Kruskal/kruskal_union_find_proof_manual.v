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
From SimpleC.EE.LLM_bench.Algorithms.Kruskal Require Import kruskal_union_find_goal.
From SimpleC.EE.LLM_bench.Algorithms.Kruskal Require Import kruskal_union_find_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope monad.
Require Import SimpleC.EE.LLM_bench.Algorithms.Kruskal.kruskal_union_find_lib.
Require Import ListLib.Base.Positional.
From SumLib Require Import ZRange.
Local Open Scope sac.

Lemma proof_of_swap_edge_entail_wit_1_split_goal_spatial : swap_edge_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_split_to_seg u_pre j_pre n l_u).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (IntArray.full_split_to_seg v_pre j_pre n l_v).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (IntArray.full_split_to_seg w_pre j_pre n l_w).
      * dump_pre_spatial; lia.
      * cancel.
Qed.

Lemma proof_of_swap_edge_entail_wit_1 : swap_edge_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_swap_edge_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_swap_edge_entail_wit_2_split_goal_spatial : swap_edge_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_split_to_seg u_pre i_pre n l_u).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (IntArray.full_split_to_seg v_pre i_pre n l_v).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (IntArray.full_split_to_seg w_pre i_pre n l_w).
      * dump_pre_spatial; lia.
      * cancel.
Qed.

Lemma proof_of_swap_edge_entail_wit_2 : swap_edge_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_swap_edge_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_swap_edge_return_wit_1_split_goal_spatial : swap_edge_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmerge : forall (l : list Z) lo hi len a b,
    0 <= lo < hi -> hi < len -> Zlength l = len ->
    replace_Znth lo a (sublist 0 hi l) ++
      replace_Znth 0 b (sublist hi len l) =
    replace_Znth hi b (replace_Znth lo a l)).
  {
    intros l lo hi len a b Hlo Hhi Hlen.
    assert (Hl : l = sublist 0 hi l ++ sublist hi len l).
    {
      symmetry.
      rewrite <- (sublist_split 0 len hi l) by lia.
      apply sublist_self.
      symmetry; exact Hlen.
    }
    rewrite Hl at 3.
    rewrite replace_Znth_app_l by
      (rewrite ?Zlength_sublist0; lia).
    assert (Hprefix_len :
      Zlength (replace_Znth lo a (sublist 0 hi l)) = hi).
    { rewrite Zlength_replace_Znth, Zlength_sublist0; lia. }
    rewrite replace_Znth_app_r by lia.
    rewrite (replace_Znth_nothing hi
      (replace_Znth lo a (sublist 0 hi l)) b) by lia.
    rewrite Hprefix_len.
    replace (hi - hi) with 0 by lia.
    reflexivity.
  }
  replace (j_pre - j_pre) with 0 by lia.
  sep_apply_l_atomic (IntArray.full_to_seg u_pre j_pre
    (replace_Znth i_pre (Znth j_pre l_u 0) (sublist 0 j_pre l_u))).
  sep_apply_l_atomic (IntArray.full_to_seg v_pre j_pre
    (replace_Znth i_pre (Znth j_pre l_v 0) (sublist 0 j_pre l_v))).
  sep_apply_l_atomic (IntArray.full_to_seg w_pre j_pre
    (replace_Znth i_pre (Znth j_pre l_w 0) (sublist 0 j_pre l_w))).
  sep_apply_l_atomic (IntArray.seg_merge_to_full u_pre 0 j_pre n
    (replace_Znth i_pre (Znth j_pre l_u 0) (sublist 0 j_pre l_u))
    (replace_Znth 0 (Znth i_pre l_u 0) (sublist j_pre n l_u))).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (IntArray.seg_merge_to_full v_pre 0 j_pre n
      (replace_Znth i_pre (Znth j_pre l_v 0) (sublist 0 j_pre l_v))
      (replace_Znth 0 (Znth i_pre l_v 0) (sublist j_pre n l_v))).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (IntArray.seg_merge_to_full w_pre 0 j_pre n
        (replace_Znth i_pre (Znth j_pre l_w 0) (sublist 0 j_pre l_w))
        (replace_Znth 0 (Znth i_pre l_w 0) (sublist j_pre n l_w))).
      * dump_pre_spatial; lia.
      * replace (u_pre + 0 * sizeof(INT)) with u_pre by lia.
        replace (v_pre + 0 * sizeof(INT)) with v_pre by lia.
        replace (w_pre + 0 * sizeof(INT)) with w_pre by lia.
        replace (n - 0) with n by lia.
        rewrite !Hmerge by lia.
        cancel.
Qed.

Lemma proof_of_swap_edge_return_wit_1 : swap_edge_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_swap_edge_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_swap_edge_return_wit_2_split_goal_spatial : swap_edge_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmerge : forall (l : list Z) lo hi len a b,
    0 <= lo < hi -> hi < len -> Zlength l = len ->
    replace_Znth lo a (sublist 0 hi l) ++
      replace_Znth 0 b (sublist hi len l) =
    replace_Znth hi b (replace_Znth lo a l)).
  {
    intros l lo hi len a b Hlo Hhi Hlen.
    assert (Hl : l = sublist 0 hi l ++ sublist hi len l).
    {
      symmetry.
      rewrite <- (sublist_split 0 len hi l) by lia.
      apply sublist_self.
      symmetry; exact Hlen.
    }
    rewrite Hl at 3.
    rewrite replace_Znth_app_l by
      (rewrite ?Zlength_sublist0; lia).
    assert (Hprefix_len :
      Zlength (replace_Znth lo a (sublist 0 hi l)) = hi).
    { rewrite Zlength_replace_Znth, Zlength_sublist0; lia. }
    rewrite replace_Znth_app_r by lia.
    rewrite (replace_Znth_nothing hi
      (replace_Znth lo a (sublist 0 hi l)) b) by lia.
    rewrite Hprefix_len.
    replace (hi - hi) with 0 by lia.
    reflexivity.
  }
  assert (Hcomm : forall (l : list Z) i j a b,
    0 <= i -> 0 <= j -> i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l)).
  {
    intros l i j a b Hi Hj Hneq.
    unfold replace_Znth.
    assert (Hcomm_nat : forall ni nj (xs : list Z),
      ni <> nj ->
      replace_nth nj (replace_nth ni xs a) b =
      replace_nth ni (replace_nth nj xs b) a).
    {
      intros ni.
      induction ni as [| ni IH]; intros nj [| x xs] Hnat; simpl.
      - destruct nj; reflexivity.
      - destruct nj; simpl.
        + contradiction Hnat; reflexivity.
        + reflexivity.
      - destruct nj; reflexivity.
      - destruct nj; simpl.
        + reflexivity.
        + f_equal. apply IH. congruence.
    }
    apply Hcomm_nat.
    intro Heq.
    apply Hneq.
    apply Z2Nat.inj in Heq; lia.
  }
  replace (i_pre - i_pre) with 0 by lia.
  sep_apply_l_atomic (IntArray.full_to_seg u_pre i_pre
    (replace_Znth j_pre (Znth i_pre l_u 0) (sublist 0 i_pre l_u))).
  sep_apply_l_atomic (IntArray.full_to_seg v_pre i_pre
    (replace_Znth j_pre (Znth i_pre l_v 0) (sublist 0 i_pre l_v))).
  sep_apply_l_atomic (IntArray.full_to_seg w_pre i_pre
    (replace_Znth j_pre (Znth i_pre l_w 0) (sublist 0 i_pre l_w))).
  sep_apply_l_atomic (IntArray.seg_merge_to_full u_pre 0 i_pre n
    (replace_Znth j_pre (Znth i_pre l_u 0) (sublist 0 i_pre l_u))
    (replace_Znth 0 (Znth j_pre l_u 0) (sublist i_pre n l_u))).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (IntArray.seg_merge_to_full v_pre 0 i_pre n
      (replace_Znth j_pre (Znth i_pre l_v 0) (sublist 0 i_pre l_v))
      (replace_Znth 0 (Znth j_pre l_v 0) (sublist i_pre n l_v))).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (IntArray.seg_merge_to_full w_pre 0 i_pre n
        (replace_Znth j_pre (Znth i_pre l_w 0) (sublist 0 i_pre l_w))
        (replace_Znth 0 (Znth j_pre l_w 0) (sublist i_pre n l_w))).
      * dump_pre_spatial; lia.
      * replace (u_pre + 0 * sizeof(INT)) with u_pre by lia.
        replace (v_pre + 0 * sizeof(INT)) with v_pre by lia.
        replace (w_pre + 0 * sizeof(INT)) with w_pre by lia.
        replace (n - 0) with n by lia.
        rewrite !Hmerge by lia.
        rewrite (Hcomm l_u j_pre i_pre
          (Znth i_pre l_u 0) (Znth j_pre l_u 0)) by lia.
        rewrite (Hcomm l_v j_pre i_pre
          (Znth i_pre l_v 0) (Znth j_pre l_v 0)) by lia.
        rewrite (Hcomm l_w j_pre i_pre
          (Znth i_pre l_w 0) (Znth j_pre l_w 0)) by lia.
        cancel.
Qed.

Lemma proof_of_swap_edge_return_wit_2 : swap_edge_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_swap_edge_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_swap_edge_return_wit_3_split_goal_1 : swap_edge_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  rewrite !replace_Znth_Znth by lia.
  reflexivity.
Qed.

Lemma proof_of_swap_edge_return_wit_3_split_goal_2 : swap_edge_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  rewrite !replace_Znth_Znth by lia.
  reflexivity.
Qed.

Lemma proof_of_swap_edge_return_wit_3_split_goal_3 : swap_edge_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  rewrite !replace_Znth_Znth by lia.
  reflexivity.
Qed.

Lemma proof_of_swap_edge_return_wit_3 : swap_edge_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_return_wit_3_split_goal_1.
  - Goal_apply proof_of_swap_edge_return_wit_3_split_goal_2.
  - Goal_apply proof_of_swap_edge_return_wit_3_split_goal_3.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_1_pure_split_goal_1 : swap_edge_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_1_pure_split_goal_2 : swap_edge_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_1_pure : swap_edge_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_2_pure_split_goal_1 : swap_edge_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_2_pure_split_goal_2 : swap_edge_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_2_pure : swap_edge_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_2_pure_split_goal_2.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_3_pure_split_goal_1 : swap_edge_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_3_pure_split_goal_2 : swap_edge_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_3_pure : swap_edge_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_4_pure_split_goal_1 : swap_edge_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_4_pure_split_goal_2 : swap_edge_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_4_pure : swap_edge_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_4_pure_split_goal_2.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_5_pure_split_goal_1 : swap_edge_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_5_pure_split_goal_2 : swap_edge_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_5_pure : swap_edge_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_6_pure_split_goal_1 : swap_edge_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_6_pure_split_goal_2 : swap_edge_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma proof_of_swap_edge_partial_solve_wit_6_pure : swap_edge_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_swap_edge_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_partitionByWeight_entail_wit_1 : partitionByWeight_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_u l_v l_w edge_order left_pre left_pre (Znth right_pre l_w 0).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    unfold same_outside_edge_arrays_range.
    intros; repeat split; reflexivity.
Qed.

Lemma proof_of_partitionByWeight_entail_wit_2_1 : partitionByWeight_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (u' := replace_Znth j_2 (Znth i_2 l_u1_2 0)
    (replace_Znth i_2 (Znth j_2 l_u1_2 0) l_u1_2)).
  set (v' := replace_Znth j_2 (Znth i_2 l_v1_2 0)
    (replace_Znth i_2 (Znth j_2 l_v1_2 0) l_v1_2)).
  set (w' := replace_Znth j_2 (Znth i_2 l_w1_2 0)
    (replace_Znth i_2 (Znth j_2 l_w1_2 0) l_w1_2)).
  set (o' := replace_Znth j_2 (Znth i_2 edge_order1_2 (-1))
    (replace_Znth i_2 (Znth j_2 edge_order1_2 (-1)) edge_order1_2)).
  assert (Hord' : edge_arrays_ordered_by n orig_u orig_v orig_w u' v' w' o').
  { unfold u', v', w', o'.
    eapply edge_arrays_ordered_swap_positions__partition_loop; eauto; lia. }
  assert (Ho_len : Zlength edge_order1_2 = n).
  { unfold edge_arrays_ordered_by in PreH15. tauto. }
  assert (Hperm_swap : Permutation edge_order1_2 o').
  { unfold o'. apply permutation_swap_Znth__partition_loop.
    - rewrite Ho_len. lia.
    - rewrite Ho_len. lia. }
  assert (Hperm' : Permutation edge_order o').
  { eapply Permutation_trans; eauto. }
  assert (Houtside' : same_outside_edge_arrays_range
    l_u l_v l_w edge_order u' v' w' o' left_pre right_pre).
  { unfold u', v', w', o'.
    eapply same_outside_edge_arrays_range_swap_inside__partition_loop;
      eauto; lia. }
  assert (Hbands :
    (forall k, left_pre <= k < i_2 + 1 -> Znth k w' 0 < pivot_w_2) /\
    (forall k, i_2 + 1 <= k < j_2 + 1 -> pivot_w_2 <= Znth k w' 0) /\
    Znth right_pre w' 0 = pivot_w_2).
  { unfold w'. eapply partition_scan_swap__partition_loop; eauto; lia. }
  destruct Hbands as [Hlow' [Hhigh' Hpivot']].
  Exists u' v' w' o' (j_2 + 1) (i_2 + 1) pivot_w_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_partitionByWeight_entail_wit_2_2 : partitionByWeight_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hhigh' : forall k, i_2 <= k < j_2 + 1 ->
    pivot_w_2 <= Znth k l_w1_2 0).
  { eapply partition_scan_step__partition_loop; eauto; lia. }
  Exists l_u1_2 l_v1_2 l_w1_2 edge_order1_2
    (j_2 + 1) i_2 pivot_w_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_partitionByWeight_return_wit_1 : partitionByWeight_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hjr : j = right_pre) by lia.
  subst j.
  set (u' := replace_Znth right_pre (Znth i l_u1_2 0)
    (replace_Znth i (Znth right_pre l_u1_2 0) l_u1_2)).
  set (v' := replace_Znth right_pre (Znth i l_v1_2 0)
    (replace_Znth i (Znth right_pre l_v1_2 0) l_v1_2)).
  set (w' := replace_Znth right_pre (Znth i l_w1_2 0)
    (replace_Znth i (Znth right_pre l_w1_2 0) l_w1_2)).
  set (o' := replace_Znth right_pre (Znth i edge_order1_2 (-1))
    (replace_Znth i (Znth right_pre edge_order1_2 (-1)) edge_order1_2)).
  assert (Hord' : edge_arrays_ordered_by n orig_u orig_v orig_w u' v' w' o').
  { unfold u', v', w', o'.
    eapply edge_arrays_ordered_swap_positions__partition_loop; eauto; lia. }
  assert (Ho_len : Zlength edge_order1_2 = n).
  { unfold edge_arrays_ordered_by in PreH14. tauto. }
  assert (Hperm_swap : Permutation edge_order1_2 o').
  { unfold o'. apply permutation_swap_Znth__partition_loop;
      rewrite Ho_len; lia. }
  assert (Hperm' : Permutation edge_order o').
  { eapply Permutation_trans; eauto. }
  assert (Houtside' : same_outside_edge_arrays_range
    l_u l_v l_w edge_order u' v' w' o' left_pre right_pre).
  { unfold u', v', w', o'.
    eapply same_outside_edge_arrays_range_swap_inside__partition_loop;
      eauto; lia. }
  assert (Hpartitioned :
    edge_arrays_partitioned_by_weight_at w' left_pre right_pre i).
  { unfold w'. eapply partition_finish_swap__partition_loop; eauto; lia. }
  Exists u' v' w' o'.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_3_pure_split_goal_1 : partitionByWeight_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold edge_arrays_ordered_by in PreH22. tauto.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_3_pure_split_goal_2 : partitionByWeight_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold edge_arrays_ordered_by in PreH22. tauto.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_3_pure_split_goal_3 : partitionByWeight_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold edge_arrays_ordered_by in PreH22. tauto.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_3_pure : partitionByWeight_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partitionByWeight_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_partitionByWeight_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_partitionByWeight_partial_solve_wit_3_pure_split_goal_3.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_4_pure_split_goal_1 : partitionByWeight_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold edge_arrays_ordered_by in PreH19. tauto.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_4_pure_split_goal_2 : partitionByWeight_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold edge_arrays_ordered_by in PreH19. tauto.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_4_pure_split_goal_3 : partitionByWeight_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold edge_arrays_ordered_by in PreH19. tauto.
Qed.

Lemma proof_of_partitionByWeight_partial_solve_wit_4_pure : partitionByWeight_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partitionByWeight_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_partitionByWeight_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_partitionByWeight_partial_solve_wit_4_pure_split_goal_3.
Qed.

Lemma proof_of_quickByWeightRange_return_wit_1 : quickByWeightRange_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hperm : Permutation edge_order edge_order1_4).
  { eapply Permutation_trans; [exact PreH18 |].
    eapply Permutation_trans; [exact PreH10 | exact PreH4]. }
  assert (Houtside : same_outside_edge_arrays_range
    l_u l_v l_w edge_order
    l_u1_4 l_v1_4 l_w1_4 edge_order1_4 left_pre right_pre).
  { eapply same_outside_edge_arrays_range_trans__quicksort_results
      with (pivot := retval); eauto; lia. }
  assert (Hsorted : edge_arrays_range_sorted_by_weight
    l_w1_4 left_pre right_pre).
  { eapply edge_arrays_range_sorted_join__quicksort_results
      with (pivot := retval)
        (bu := l_u1_2) (bv := l_v1_2) (bo := edge_order1_2)
        (cu := l_u1_3) (cv := l_v1_3) (co := edge_order1_3)
        (du := l_u1_4) (dv := l_v1_4) (do_ := edge_order1_4)
        (orig_u := orig_u) (orig_v := orig_v) (orig_w := orig_w);
      eauto; lia. }
  Exists l_u1_4 l_v1_4 l_w1_4 edge_order1_4.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_quickByWeightRange_return_wit_2 : quickByWeightRange_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_u l_v l_w edge_order.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try apply Permutation_refl;
      try (unfold same_outside_edge_arrays_range; intros; repeat split; reflexivity);
      try (eapply edge_arrays_range_sorted_vacuous__quicksort_results; lia).
Qed.

Lemma proof_of_quickByWeight_return_wit_1 : quickByWeight_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Horder_len : Zlength edge_order1_2 = n_pre).
  { unfold edge_arrays_ordered_by in PreH3. tauto. }
  assert (Hsorted : edge_arrays_sorted_by_weight l_w1_2 edge_order1_2).
  { eapply edge_arrays_sorted_full_range__quicksort_results; eauto. }
  Exists l_u1_2 l_v1_2 l_w1_2 edge_order1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold after_sorted_edge_of_input; tauto.
Qed.

Lemma proof_of_quickByWeight_return_wit_2 : quickByWeight_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hn : n_pre = 0) by lia.
  assert (Horder_len : Zlength edge_order = n_pre).
  { unfold edge_arrays_ordered_by in PreH4. tauto. }
  assert (Hsorted : edge_arrays_sorted_by_weight l_w edge_order).
  { eapply edge_arrays_sorted_full_range__quicksort_results; eauto.
    eapply edge_arrays_range_sorted_vacuous__quicksort_results; lia. }
  Exists l_u l_v l_w edge_order.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try apply Permutation_refl.
    unfold after_sorted_edge_of_input; tauto.
Qed.

Lemma proof_of_kruskal_entail_wit_2 : kruskal_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  - pose proof (kruskal_initial_scan_state__kruskal_init
      n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec
      orig_w_low_level_spec g_low_level_spec edge_order_2
      (initSt g_low_level_spec) X_low_level_spec
      PreH3 PreH7 PreH8 eq_refl PreH10)
      as [Hscan [Hphase [Hconnect [Houtput Hsafe]]]].
    assert (Hconnect_repr :
      union_find_connectivity_matches_state
        g_low_level_spec (initSt g_low_level_spec) repr_of_2).
    {
      intros x y Hx Hy.
      specialize (Hconnect x y Hx Hy).
      rewrite (PreH2 x).
      rewrite (PreH2 y).
      - exact Hconnect.
      - eapply array_graph_vertex_in_uf_domain; eauto.
      - eapply array_graph_vertex_in_uf_domain; eauto.
    }
    Exists repr_of_2 (initSt g_low_level_spec) l_u_sorted l_v_sorted
      l_w_sorted edge_order_2.
    split_pure_spatial.
    + repeat cancel.
    + split_pures;
        try (dump_pre_spatial; assumption);
        try (dump_pre_spatial; exact Hscan);
        try (dump_pre_spatial; exact Hphase);
        try (dump_pre_spatial; exact Hconnect_repr);
        try (dump_pre_spatial; exact Houtput);
        try (dump_pre_spatial; exact Hsafe);
        try (dump_pre_spatial; reflexivity);
        try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_3 : kruskal_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists retval_3 retval_2 retval uf_2
    (@nil Z) (@nil Z) (@nil Z) repr_of_2 s_2
    l_u_2 l_v_2 l_w_2 edge_order_2 0 0.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.undef_full_to_undef_seg retval (n_pre - 1)).
    sep_apply_l_atomic
      (IntArray.undef_full_to_undef_seg retval_2 (n_pre - 1)).
    sep_apply_l_atomic
      (IntArray.undef_full_to_undef_seg retval_3 (n_pre - 1)).
    rewrite (IntArray.seg_empty retval 0 0).
    rewrite (IntArray.seg_empty retval_2 0 0).
    rewrite (IntArray.seg_empty retval_3 0 0).
    cancel (((&( "i" ))) # Int |-> 0).
    cancel (((&( "m" ))) # Int |-> m_pre).
    cancel (((&( "chosen" ))) # Int |-> 0).
    cancel (((&( "n" ))) # Int |-> n_pre).
    cancel (((&( "u" ))) # Ptr |-> u_pre).
    cancel (((&( "v" ))) # Ptr |-> v_pre).
    cancel (((&( "w" ))) # Ptr |-> w_pre).
    cancel (((&( "uf" ))) # Ptr |-> uf_2).
    cancel (UF uf_2 n_pre repr_of_2).
    cancel (IntArray.full u_pre m_pre l_u_2).
    cancel (IntArray.full v_pre m_pre l_v_2).
    cancel (IntArray.full w_pre m_pre l_w_2).
    cancel (((&( "out_u" ))) # Ptr |-> retval).
    cancel (IntArray.undef_seg retval 0 (n_pre - 1)).
    cancel (((&( "out_v" ))) # Ptr |-> retval_2).
    cancel (IntArray.undef_seg retval_2 0 (n_pre - 1)).
    cancel (((&( "out_w" ))) # Ptr |-> retval_3).
    cancel (IntArray.undef_seg retval_3 0 (n_pre - 1)).
    split_pure_spatial.
    + cancel.
    + split_pures; apply derivable1s_coq_prop_r; reflexivity.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_4 : kruskal_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (sorted_edge_endpoints_range__kruskal_scan_control
      n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec
      orig_w_low_level_spec l_u l_v l_w edge_order_2
      g_low_level_spec i PreH11 PreH12 PreH13 ltac:(lia))
    as [[Hu_lo Hu_hi] [Hv_lo Hv_hi]].
  Exists l_out_u_2 l_out_v_2 l_out_w_2 repr_of_2 s_2 edge_order_2
    l_w l_v l_u.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_5 : kruskal_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_out_u_2 l_out_v_2 l_out_w_2 s_2 edge_order_2 repr_of_2
    l_w_2 l_v_2 l_u_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_6 : kruskal_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_out_u_2 l_out_v_2 l_out_w_2 s_2 edge_order_2 repr_of_2
    l_w_2 l_v_2 l_u_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_7 : kruskal_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst edge_u edge_v edge_w.
  assert (Hrepr_neq :
      repr_of_2 (Znth i l_u_2 0) <> repr_of_2 (Znth i l_v_2 0)).
  { congruence. }
  pose proof (kruskal_graph_valid g_low_level_spec PreH26) as Hg.
  pose proof (selected_sorted_edge__kruskal_selected_transition
    n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec
    orig_w_low_level_spec g_low_level_spec l_u_2 l_v_2 l_w_2
    edge_order_2 i chosen s_2 repr_of_2 PreH25 PreH27 Hg PreH28 PreH30
    Hrepr_neq ltac:(lia)) as [Hselected [Hpair Hweight]].
  pose proof (kruskal_union_add_edge_transition__kruskal_selected_transition
    g_low_level_spec edge_order_2 i chosen s_2
    (Znth i l_u_2 0) (Znth i l_v_2 0) (Znth i edge_order_2 (-1))
    PreH26 PreH28 Hselected Hpair
    ltac:(rewrite (array_graph_edge_count _ _ _ _ _ _ PreH25); lia)
    ltac:(rewrite (array_graph_vertex_count _ _ _ _ _ _ PreH25); lia))
    as [Hadd [Hscan_next Hphase_next]].
  pose proof PreH28 as Hscan_old.
  destruct Hscan_old as [_ [_ [_ [_ [Hgreedy_old _]]]]].
  destruct Hgreedy_old as [_ [_ [Hvalid_old Hvertex_old]]].
  pose proof (selected_edge_not_in_forest__kruskal_selected_transition
    g_low_level_spec edge_order_2 i chosen s_2 (Znth i edge_order_2 (-1))
    Hvalid_old PreH28 Hselected) as Hnew.
  pose proof (add_edge_uf_merge_connectivity__kruskal_selected_transition
    n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec
    orig_w_low_level_spec g_low_level_spec s_2 repr_of_2 repr_of1_2
    (Znth i l_u_2 0) (Znth i l_v_2 0) (Znth i edge_order_2 (-1))
    PreH25 Hvalid_old Hvertex_old PreH30 PreH1 Hpair Hnew)
    as Hconn_next.
  pose proof (output_prefix_matches_state_append__kruskal_selected_transition
    g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2
    (Znth i l_u_2 0) (Znth i l_v_2 0) (Znth i l_w_2 0)
    (Znth i edge_order_2 (-1)) PreH31 Hvalid_old Hnew Hpair Hweight)
    as Hout_next.
  pose proof (safeExec_kruskal_selected_step__kruskal_selected_transition
    g_low_level_spec edge_order_2 i s_2
    {| Kruskal.graph_in_state := add_edge_graph s_2.(Kruskal.graph_in_state)
       (Znth i l_u_2 0) (Znth i l_v_2 0) (Znth i edge_order_2 (-1)) |}
    (Znth i edge_order_2 (-1)) (Znth i l_u_2 0) (Znth i l_v_2 0)
    X_low_level_spec Hselected Hpair Hadd PreH32) as Hsafe_next.
  assert (Hufdiff :
    uf_different_class repr_of_2 (Znth i l_u_2 0) (Znth i l_v_2 0)).
  { unfold uf_different_class. exact Hrepr_neq. }
  Exists (l_out_u_2 ++ Znth i l_u_2 0 :: nil).
  Exists (l_out_v_2 ++ Znth i l_v_2 0 :: nil).
  Exists (l_out_w_2 ++ Znth i l_w_2 0 :: nil).
  Exists repr_of1_2.
  Exists {| Kruskal.graph_in_state := add_edge_graph s_2.(Kruskal.graph_in_state)
       (Znth i l_u_2 0) (Znth i l_v_2 0) (Znth i edge_order_2 (-1)) |}.
  Exists (Znth i edge_order_2 (-1)).
  Exists l_out_u_2 l_out_v_2 l_out_w_2 s_2 edge_order_2 repr_of_2.
  Exists l_w_2 l_v_2 l_u_2.
  split_pure_spatial.
  - cancel (IntArray.full u_pre m_pre l_u_2).
    cancel (IntArray.full v_pre m_pre l_v_2).
    cancel (IntArray.full w_pre m_pre l_w_2).
    cancel (UF uf n_pre repr_of1_2).
    cancel (IntArray.seg out_u 0 (chosen + 1)
      (l_out_u_2 ++ Znth i l_u_2 0 :: nil)).
    cancel (IntArray.undef_seg out_u (chosen + 1) (n_pre - 1)).
    cancel (IntArray.seg out_v 0 (chosen + 1)
      (l_out_v_2 ++ Znth i l_v_2 0 :: nil)).
    cancel (IntArray.undef_seg out_v (chosen + 1) (n_pre - 1)).
    cancel (IntArray.seg out_w 0 (chosen + 1)
      (l_out_w_2 ++ Znth i l_w_2 0 :: nil)).
    cancel (IntArray.undef_seg out_w (chosen + 1) (n_pre - 1)).
  - split_pures; dump_pre_spatial;
      try solve [auto | lia | exact Hselected | exact Hpair |
        exact Hadd | exact PreH1 | exact Hscan_next | exact Hphase_next |
        exact Hconn_next | exact Hout_next | exact Hsafe_next |
        exact Hufdiff].
    all: replace (chosen + 1 - 1) with chosen by lia; assumption.
Qed.

Lemma proof_of_kruskal_entail_wit_8 : kruskal_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrepr_eq :
      repr_of_2 (Znth i l_u_2 0) = repr_of_2 (Znth i l_v_2 0)).
  { rewrite <- PreH7, <- PreH8. congruence. }
  assert (Hsame : uf_same_class repr_of_2 edge_u edge_v).
  { unfold uf_same_class, same_class. congruence. }
  pose proof
    (scanned_prefix_extend_nonselectable__kruskal_scan_control
      n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec
      orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2
      g_low_level_spec i chosen s_2 repr_of_2
      PreH24 PreH25 PreH26 PreH27 PreH29 ltac:(lia) Hrepr_eq)
    as Hscan_next.
  Exists l_out_u_2 l_out_v_2 l_out_w_2 s_2 edge_order_2 repr_of_2
    l_w_2 l_v_2 l_u_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [auto | lia | exact Hsame | exact Hscan_next].
Qed.

Lemma proof_of_kruskal_entail_wit_9_1 : kruskal_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_out_u1 l_out_v1 l_out_w1 repr_of1 s_next edge_order_2
    l_w_2 l_v_2 l_u_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_9_2 : kruskal_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_out_u_2 l_out_v_2 l_out_w_2 repr_of s edge_order_2
    l_w_2 l_v_2 l_u_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_10 : kruskal_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists out_w_2 out_v_2 out_u_2 uf_2
    l_out_u_2 l_out_v_2 l_out_w_2 repr_of_after s_after
    l_u_2 l_v_2 l_w_2 edge_order_2 chosen_2 (i_2 + 1).
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_11_1 : kruskal_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchosen : chosen = n_pre - 1).
  {
    eapply kruskal_exhausted_scan_complete__kruskal_exit_result; eauto.
  }
  subst chosen.
  repeat rewrite IntArray.undef_seg_empty.
  sep_apply_l_atomic (IntArray.seg_to_full out_u 0 (n_pre - 1) l_out_u_2).
  sep_apply_l_atomic (IntArray.seg_to_full out_v 0 (n_pre - 1) l_out_v_2).
  sep_apply_l_atomic (IntArray.seg_to_full out_w 0 (n_pre - 1) l_out_w_2).
  replace (out_u + 0 * sizeof ( INT )) with out_u by lia.
  replace (out_v + 0 * sizeof ( INT )) with out_v by lia.
  replace (out_w + 0 * sizeof ( INT )) with out_w by lia.
  repeat rewrite Z.sub_0_r.
  Exists l_out_u_2 l_out_v_2 l_out_w_2 repr_of_2 s_2
    l_u_2 l_v_2 l_w_2 edge_order_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_entail_wit_11_2 : kruskal_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchosen : chosen = n_pre - 1) by lia.
  subst chosen.
  repeat rewrite IntArray.undef_seg_empty.
  sep_apply_l_atomic (IntArray.seg_to_full out_u 0 (n_pre - 1) l_out_u_2).
  sep_apply_l_atomic (IntArray.seg_to_full out_v 0 (n_pre - 1) l_out_v_2).
  sep_apply_l_atomic (IntArray.seg_to_full out_w 0 (n_pre - 1) l_out_w_2).
  replace (out_u + 0 * sizeof ( INT )) with out_u by lia.
  replace (out_v + 0 * sizeof ( INT )) with out_v by lia.
  replace (out_w + 0 * sizeof ( INT )) with out_w by lia.
  repeat rewrite Z.sub_0_r.
  Exists l_out_u_2 l_out_v_2 l_out_w_2 repr_of_2 s_2
    l_u_2 l_v_2 l_w_2 edge_order_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_kruskal_return_wit_1 : kruskal_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hresult :
    kruskal_result_graph_matches_array l_out_u l_out_v l_out_w
      g_low_level_spec s.(Kruskal.graph_in_state)).
  {
    eapply kruskal_completed_output_graph__kruskal_exit_result; eauto.
  }
  assert (Hcomplete : ~ exists e, state_selectable_edge g_low_level_spec s e).
  {
    eapply kruskal_scan_phase_complete; [exact PreH13 |].
    rewrite (array_graph_vertex_count _ _ _ _ _ _ PreH9).
    exact PreH4.
  }
  assert (Hsafe :
    safeExec
      (kruskal_state_graph_matches s.(Kruskal.graph_in_state))
      (return tt) X_low_level_spec).
  {
    eapply safeExec_Kruskal_complete_return__kruskal_exit_result; eauto.
  }
  Exists out_w out_v out_u l_out_u l_out_v l_out_w.
  Exists l_u_2 l_v_2 l_w_2 edge_order_2 s.(Kruskal.graph_in_state).
  split_pure_spatial.
  - cancel (&(retval # "mst_tree" ->ₛ "ru") # Ptr |-> out_u).
    cancel (&(retval # "mst_tree" ->ₛ "rv") # Ptr |-> out_v).
    cancel (&(retval # "mst_tree" ->ₛ "rw") # Ptr |-> out_w).
    cancel (IntArray.full u_pre m_pre l_u_2).
    cancel (IntArray.full v_pre m_pre l_v_2).
    cancel (IntArray.full w_pre m_pre l_w_2).
    cancel (IntArray.full out_u (n_pre - 1) l_out_u).
    cancel (IntArray.full out_v (n_pre - 1) l_out_v).
    cancel (IntArray.full out_w (n_pre - 1) l_out_w).
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hsafe);
      try (dump_pre_spatial; exact Hresult).
Qed.

Lemma proof_of_kruskal_derive_high_level_spec_by_low_level_spec : kruskal_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (safeExec_kruskal_return_is_mst__high_level_refinement
       g_high_level_spec g_high_level_spec H4) as [Hsafe _].
  Exists orig_u_high_level_spec orig_v_high_level_spec
    orig_w_high_level_spec g_high_level_spec
    (fun _ s => return_is_mst g_high_level_spec
       s.(Kruskal.graph_in_state)).
  split_pure_spatial.
  - cancel (IntArray.full u_pre m_pre orig_u_high_level_spec).
    cancel (IntArray.full v_pre m_pre orig_v_high_level_spec).
    cancel (IntArray.full w_pre m_pre orig_w_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros retval_rw_2 retval_rv_2 retval_ru_2 lru_2 lrv_2 lrw_2
      l_u_2 l_v_2 l_w_2 edge_order_2 rg_2 retval_2.
    Exists retval_rw_2 retval_rv_2 retval_ru_2 lru_2 lrv_2 lrw_2
      l_u_2 l_v_2 l_w_2 edge_order_2 rg_2 retval_2.
    repeat (split_pure_spatial || split_pures).
    + cancel (IntArray.full u_pre m_pre l_u_2).
      cancel (IntArray.full v_pre m_pre l_v_2).
      cancel (IntArray.full w_pre m_pre l_w_2).
      cancel ((&((retval_2) # "mst_tree" ->ₛ "ru")) # Ptr |-> retval_ru_2).
      cancel (IntArray.full retval_ru_2 (n_pre - 1) lru_2).
      cancel ((&((retval_2) # "mst_tree" ->ₛ "rv")) # Ptr |-> retval_rv_2).
      cancel (IntArray.full retval_rv_2 (n_pre - 1) lrv_2).
      cancel ((&((retval_2) # "mst_tree" ->ₛ "rw")) # Ptr |-> retval_rw_2).
      cancel (IntArray.full retval_rw_2 (n_pre - 1) lrw_2).
    + dump_pre_spatial.
      pose proof
        (safeExec_kruskal_return_is_mst__high_level_refinement
           g_high_level_spec rg_2 H4) as [_ Hreturn_rg].
      apply Hreturn_rg; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
  - repeat (split_pure_spatial || split_pures); dump_pre_spatial; assumption.
Qed.
