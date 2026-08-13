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
From SimpleC.EE.QCP_demos_LLM Require Import three_d_graph_field_one_read_goal.
From SimpleC.EE.QCP_demos_LLM Require Import three_d_graph_field_one_read_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_touch_graph_one_read_return_wit_1_split_goal_spatial : touch_graph_one_read_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite replace_Znth_Znth.
  pose proof (IntArray2.missing_i_merge_to_full
    (&((box_pre) # "GraphBox" ->ₛ "graph") +
      0 * (sizeof (INT) * 4 * 3))
    0 3 4 (Znth 0 cubes __default__List__List_Z)
    (Znth 0 (Znth 0 cubes __default__List__List_Z)
      __default__List_Z)) as Hrow.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr
      (&((box_pre) # "GraphBox" ->ₛ "graph") +
        0 * (sizeof (INT) * 4 * 3)) 4 0)
    4 (Znth 0 (Znth 0 cubes __default__List__List_Z)
      __default__List_Z)) with
    (IntArray.full
      ((&((box_pre) # "GraphBox" ->ₛ "graph") +
        0 * (sizeof (INT) * 4 * 3)) + 0 * 4 * sizeof (INT))
      4 (Znth 0 (Znth 0 cubes __default__List__List_Z)
        __default__List_Z)) in Hrow.
  replace (&((box_pre) # "GraphBox" ->ₛ "graph") +
      0 * (sizeof (INT) * 4 * 3) + 0 * (sizeof (INT) * 4)) with
    ((&((box_pre) # "GraphBox" ->ₛ "graph") +
      0 * (sizeof (INT) * 4 * 3)) + 0 * 4 * sizeof (INT)) by
      (rewrite sizeof_int; lia).
  sep_apply Hrow; try lia.
  rewrite replace_Znth_Znth.
  pose proof (IntArray3.missing_i_merge_to_full
    &((box_pre) # "GraphBox" ->ₛ "graph") 0 2 3 4 cubes
    (Znth 0 cubes __default__List__List_Z)) as Hmerge.
  change (IntArray3.PlaneArray.full
    (IntArray3.plane_addr &((box_pre) # "GraphBox" ->ₛ "graph") 3 4 0)
    3 4 (Znth 0 cubes __default__List__List_Z)) with
    (IntArray2.full
      (&((box_pre) # "GraphBox" ->ₛ "graph") + 0 * 3 * 4 * sizeof (INT))
      3 4 (Znth 0 cubes __default__List__List_Z)) in Hmerge.
  replace (&((box_pre) # "GraphBox" ->ₛ "graph") +
      0 * (sizeof (INT) * 4 * 3)) with
    (&((box_pre) # "GraphBox" ->ₛ "graph") +
      0 * 3 * 4 * sizeof (INT)) by (rewrite sizeof_int; lia).
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth.
  cancel.
Qed.

Lemma proof_of_touch_graph_one_read_return_wit_1 : touch_graph_one_read_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_touch_graph_one_read_return_wit_1_split_goal_spatial.
Qed.
