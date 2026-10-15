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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 15: remaining safety proofs. *)
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part1.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part2.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part3.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part4.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part5.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part6.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part7.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part8.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part9.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part10.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part11.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part12.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part13.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_proof_manual_part14.

Lemma proof_of_solver_safety_wit_1_split_goal_1 : solver_safety_wit_1_split_goal_1.
Proof.
  (* Keep this proof independently timed from the previous-round byte cache. *)
  LLM_pre_process ltac:(
    unfold Zmin in *;
    pose proof (Z.le_min_r n_pre 10);
    lia).
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_2 : solver_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_31_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_31_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_45_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_45_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_51_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_51_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_57_split_goal_1 : solver_safety_wit_57_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353))] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hrem;
      apply Z.abs_lt in Hrem
  end.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_57_split_goal_2 : solver_safety_wit_57_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353))] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hrem;
      apply Z.abs_lt in Hrem
  end.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_57_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_57_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_63_split_goal_1 : solver_safety_wit_63_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353))] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hrem;
      apply Z.abs_lt in Hrem
  end.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_63_split_goal_2 : solver_safety_wit_63_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353))] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hrem;
      apply Z.abs_lt in Hrem
  end.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_63_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_63_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_1 : solver_safety_wit_69_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_2 : solver_safety_wit_69_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_74_split_goal_1 : solver_safety_wit_74_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_74_split_goal_2 : solver_safety_wit_74_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_74_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_74_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_79_split_goal_1 : solver_safety_wit_79_split_goal_1.
Proof.
  (* Keep preprocessing arithmetic deterministic and bounded. *)
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_79_split_goal_2 : solver_safety_wit_79_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_79_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_79_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_84_split_goal_1 : solver_safety_wit_84_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_84_split_goal_2 : solver_safety_wit_84_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : P082ColumnProgress _ _ _ _ _ _ |- _ =>
      destruct H as [[[Hdl [Hpl [Hrange [Hbase1 Hbase0]]]] Hold] Hcur]
  end.
  pose proof (Hrange ((i - 1) * W + j) ltac:(rewrite Hdl; lia)) as [_ Hpref].
  rewrite (Znth_replace_Znth_Same 0 dl) by (rewrite Hdl; lia).
  match goal with
  | |- context [((?r % 998244353 + 998244353) % 998244353)] =>
      pose proof (Z.rem_bound_abs r 998244353 ltac:(lia)) as Hinner;
      apply Z.abs_lt in Hinner;
      pose proof (Z.rem_bound_pos (r % 998244353 + 998244353) 998244353
        ltac:(lia) ltac:(lia)) as Houter
  end.
  dump_pre_spatial.
  unfold P082Modulus in Hpref.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_84_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_84_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_96_split_goal_1 : solver_safety_wit_96_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  unfold P082SemanticColumns in PreH21.
  pose proof (PreH21 k_pre n_pre ltac:(lia) ltac:(lia)) as Hcell1.
  pose proof (PreH21 (k_pre - 1) (n_pre - 2) ltac:(lia) ltac:(lia)) as Hcell2.
  pose proof (PreH21 k_pre (n_pre - 2) ltac:(lia) ltac:(lia)) as Hcell3.
  unfold P082SemanticCell in Hcell1, Hcell2, Hcell3.
  destruct Hcell1 as [Hcell1 _].
  destruct Hcell2 as [Hcell2 _].
  destruct Hcell3 as [Hcell3 _].
  unfold P082Index in Hcell1, Hcell2, Hcell3.
  pose proof (P082Norm_range
    (if Z_lt_dec k_pre k_pre
     then P082ExactCoreCount n_pre k_pre
     else P082SaturatedCoreCount n_pre k_pre)) as Hr1.
  pose proof (P082Norm_range
    (if Z_lt_dec (k_pre - 1) k_pre
     then P082ExactCoreCount (n_pre - 2) (k_pre - 1)
     else P082SaturatedCoreCount (n_pre - 2) k_pre)) as Hr2.
  pose proof (P082Norm_range
    (if Z_lt_dec k_pre k_pre
     then P082ExactCoreCount (n_pre - 2) k_pre
     else P082SaturatedCoreCount (n_pre - 2) k_pre)) as Hr3.
  rewrite <- Hcell1 in Hr1.
  rewrite <- Hcell2 in Hr2.
  rewrite <- Hcell3 in Hr3.
  unfold P082Modulus in Hr1, Hr2, Hr3.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_96_split_goal_2 : solver_safety_wit_96_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  unfold P082SemanticColumns in PreH21.
  pose proof (PreH21 k_pre n_pre ltac:(lia) ltac:(lia)) as Hcell1.
  pose proof (PreH21 (k_pre - 1) (n_pre - 2) ltac:(lia) ltac:(lia)) as Hcell2.
  pose proof (PreH21 k_pre (n_pre - 2) ltac:(lia) ltac:(lia)) as Hcell3.
  unfold P082SemanticCell in Hcell1, Hcell2, Hcell3.
  destruct Hcell1 as [Hcell1 _].
  destruct Hcell2 as [Hcell2 _].
  destruct Hcell3 as [Hcell3 _].
  unfold P082Index in Hcell1, Hcell2, Hcell3.
  pose proof (P082Norm_range
    (if Z_lt_dec k_pre k_pre
     then P082ExactCoreCount n_pre k_pre
     else P082SaturatedCoreCount n_pre k_pre)) as Hr1.
  pose proof (P082Norm_range
    (if Z_lt_dec (k_pre - 1) k_pre
     then P082ExactCoreCount (n_pre - 2) (k_pre - 1)
     else P082SaturatedCoreCount (n_pre - 2) k_pre)) as Hr2.
  pose proof (P082Norm_range
    (if Z_lt_dec k_pre k_pre
     then P082ExactCoreCount (n_pre - 2) k_pre
     else P082SaturatedCoreCount (n_pre - 2) k_pre)) as Hr3.
  rewrite <- Hcell1 in Hr1.
  rewrite <- Hcell2 in Hr2.
  rewrite <- Hcell3 in Hr3.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_96 : solver_safety_wit_96.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_96_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_96_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_98_split_goal_1 : solver_safety_wit_98_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  unfold P082SemanticColumns in PreH21.
  pose proof (PreH21 k_pre n_pre ltac:(lia) ltac:(lia)) as Hcell1.
  pose proof (PreH21 (k_pre - 1) (n_pre - 2) ltac:(lia) ltac:(lia)) as Hcell2.
  unfold P082SemanticCell in Hcell1, Hcell2.
  destruct Hcell1 as [Hcell1 _].
  destruct Hcell2 as [Hcell2 _].
  unfold P082Index in Hcell1, Hcell2.
  pose proof (P082Norm_range
    (if Z_lt_dec k_pre k_pre
     then P082ExactCoreCount n_pre k_pre
     else P082SaturatedCoreCount n_pre k_pre)) as Hr1.
  pose proof (P082Norm_range
    (if Z_lt_dec (k_pre - 1) k_pre
     then P082ExactCoreCount (n_pre - 2) (k_pre - 1)
     else P082SaturatedCoreCount (n_pre - 2) k_pre)) as Hr2.
  rewrite <- Hcell1 in Hr1.
  rewrite <- Hcell2 in Hr2.
  unfold P082Modulus in Hr1, Hr2.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_98_split_goal_2 : solver_safety_wit_98_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  unfold P082SemanticColumns in PreH21.
  pose proof (PreH21 k_pre n_pre ltac:(lia) ltac:(lia)) as Hcell1.
  pose proof (PreH21 (k_pre - 1) (n_pre - 2) ltac:(lia) ltac:(lia)) as Hcell2.
  unfold P082SemanticCell in Hcell1, Hcell2.
  destruct Hcell1 as [Hcell1 _].
  destruct Hcell2 as [Hcell2 _].
  unfold P082Index in Hcell1, Hcell2.
  pose proof (P082Norm_range
    (if Z_lt_dec k_pre k_pre
     then P082ExactCoreCount n_pre k_pre
     else P082SaturatedCoreCount n_pre k_pre)) as Hr1.
  pose proof (P082Norm_range
    (if Z_lt_dec (k_pre - 1) k_pre
     then P082ExactCoreCount (n_pre - 2) (k_pre - 1)
     else P082SaturatedCoreCount (n_pre - 2) k_pre)) as Hr2.
  rewrite <- Hcell1 in Hr1.
  rewrite <- Hcell2 in Hr2.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_98 : solver_safety_wit_98.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_98_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_98_split_goal_2.
Qed.
