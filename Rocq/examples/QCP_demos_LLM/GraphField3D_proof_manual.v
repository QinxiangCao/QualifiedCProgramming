From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.QCP_demos_LLM Require Import GraphField3D_goal.
From SimpleC.EE.QCP_demos_LLM Require Import GraphField3D_proof_auto.
Import naive_C_Rules.
Local Open Scope sac.

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
