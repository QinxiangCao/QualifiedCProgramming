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
From SimpleC.EE.QCP_demos_LLM Require Import three_d_graph_field_goal.
From SimpleC.EE.QCP_demos_LLM Require Import three_d_graph_field_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_touch_plane_entail_wit_3_split_goal_spatial : touch_plane_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite replace_Znth_Znth.
  pose proof (IntArray2.missing_i_merge_to_full
    plane_pre i 3 4 plane_rows
    (Znth i plane_rows __default__List_Z)) as Hrow.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr plane_pre 4 i) 4
    (Znth i plane_rows __default__List_Z)) with
    (IntArray.full (plane_pre + i * 4 * sizeof (INT)) 4
      (Znth i plane_rows __default__List_Z)) in Hrow.
  replace (plane_pre + i * (sizeof (INT) * 4)) with
    (plane_pre + i * 4 * sizeof (INT)) by (rewrite sizeof_int; lia).
  sep_apply Hrow; try lia.
  rewrite replace_Znth_Znth.
  cancel.
Qed.

Lemma proof_of_touch_plane_entail_wit_3 : touch_plane_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_touch_plane_entail_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_touch_graph_direct_entail_wit_4_split_goal_spatial : touch_graph_direct_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite replace_Znth_Znth.
  pose proof (IntArray2.missing_i_merge_to_full
    (&((box_pre) # "GraphBox" ->ₛ "graph") +
      i * (sizeof (INT) * 4 * 3))
    j 3 4 (Znth i cubes __default__List__List_Z)
    (Znth j (Znth i cubes __default__List__List_Z)
      __default__List_Z)) as Hrow.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr
      (&((box_pre) # "GraphBox" ->ₛ "graph") +
        i * (sizeof (INT) * 4 * 3)) 4 j)
    4 (Znth j (Znth i cubes __default__List__List_Z)
      __default__List_Z)) with
    (IntArray.full
      ((&((box_pre) # "GraphBox" ->ₛ "graph") +
        i * (sizeof (INT) * 4 * 3)) + j * 4 * sizeof (INT))
      4 (Znth j (Znth i cubes __default__List__List_Z)
        __default__List_Z)) in Hrow.
  replace ((&((box_pre) # "GraphBox" ->ₛ "graph") +
      i * (sizeof (INT) * 4 * 3)) + j * (sizeof (INT) * 4)) with
    ((&((box_pre) # "GraphBox" ->ₛ "graph") +
      i * (sizeof (INT) * 4 * 3)) + j * 4 * sizeof (INT)) by
      (rewrite sizeof_int; lia).
  sep_apply Hrow; try lia.
  rewrite replace_Znth_Znth.
  pose proof (IntArray3.missing_i_merge_to_full
    &((box_pre) # "GraphBox" ->ₛ "graph") i 2 3 4 cubes
    (Znth i cubes __default__List__List_Z)) as Hmerge.
  change (IntArray3.PlaneArray.full
    (IntArray3.plane_addr
      &((box_pre) # "GraphBox" ->ₛ "graph") 3 4 i)
    3 4 (Znth i cubes __default__List__List_Z)) with
    (IntArray2.full
      (&((box_pre) # "GraphBox" ->ₛ "graph") +
        i * 3 * 4 * sizeof (INT))
      3 4 (Znth i cubes __default__List__List_Z)) in Hmerge.
  replace (&((box_pre) # "GraphBox" ->ₛ "graph") +
      i * (sizeof (INT) * 4 * 3)) with
    (&((box_pre) # "GraphBox" ->ₛ "graph") +
      i * 3 * 4 * sizeof (INT)) by (rewrite sizeof_int; lia).
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth.
  cancel.
Qed.

Lemma proof_of_touch_graph_direct_entail_wit_4 : touch_graph_direct_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_touch_graph_direct_entail_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_touch_graph_plane_partial_solve_wit_1_pure_split_goal_1 : touch_graph_plane_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (IntArray3.full_split_to_missing_i
    &((box_pre) # "GraphBox" ->ₛ "graph") layer_pre 2 3 4 cubes); try lia.
  prop_apply (IntArray3.PlaneArray.full_Zlength
    (IntArray3.plane_addr &((box_pre) # "GraphBox" ->ₛ "graph") 3 4 layer_pre)
    3 4 (Znth layer_pre cubes nil)).
  Intros_p Hplane_length.
  dump_pre_spatial.
  rewrite (Znth_indep cubes layer_pre __default__List__List_Z nil) by lia.
  exact Hplane_length.
Qed.

Lemma proof_of_touch_graph_plane_partial_solve_wit_1_pure : touch_graph_plane_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_touch_graph_plane_partial_solve_wit_1_pure_split_goal_1.
Qed.
