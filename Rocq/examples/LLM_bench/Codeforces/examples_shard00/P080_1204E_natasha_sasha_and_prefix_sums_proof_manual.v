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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P080_1204E_natasha_sasha_and_prefix_sums_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P080_1204E_natasha_sasha_and_prefix_sums_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P080_1204E_natasha_sasha_and_prefix_sums_lib.
Local Open Scope sac.

Lemma proof_of_modpow_entail_wit_1_split_goal_1 : modpow_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma proof_of_modpow_entail_wit_1 : modpow_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modpow_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_modpow_entail_wit_2_1_split_goal_1 : modpow_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite P080_odd_step__modpow by (assumption || lia). exact PreH9.
Qed.

Lemma proof_of_modpow_entail_wit_2_1_split_goal_2 : modpow_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (Z.rem_bound_pos (r*a) 998244853 ltac:(nia) ltac:(lia)); lia.
Qed.

Lemma proof_of_modpow_entail_wit_2_1_split_goal_3 : modpow_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (Z.rem_bound_pos (r*a) 998244853 ltac:(nia) ltac:(lia)); lia.
Qed.

Lemma proof_of_modpow_entail_wit_2_1_split_goal_4 : modpow_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (Z.rem_bound_pos (a*a) 998244853 ltac:(nia) ltac:(lia)); lia.
Qed.

Lemma proof_of_modpow_entail_wit_2_1_split_goal_5 : modpow_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (Z.rem_bound_pos (a*a) 998244853 ltac:(nia) ltac:(lia)); lia.
Qed.

Lemma proof_of_modpow_entail_wit_2_1_split_goal_6 : modpow_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite (proj1 (P080_parity_shift__modpow e)).
  apply Z.le_trans with e; [apply Z.div_le_upper_bound; lia | exact PreH2].
Qed.

Lemma proof_of_modpow_entail_wit_2_1_split_goal_7 : modpow_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(idtac).
  apply Z.shiftr_nonneg. exact PreH1.
Qed.

Lemma proof_of_modpow_entail_wit_2_1 : modpow_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_6.
  - Goal_apply proof_of_modpow_entail_wit_2_1_split_goal_7.
Qed. 

Lemma proof_of_modpow_entail_wit_2_2_split_goal_1 : modpow_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite P080_even_step__modpow by (assumption || lia). exact PreH9.
Qed.

Lemma proof_of_modpow_entail_wit_2_2_split_goal_2 : modpow_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (Z.rem_bound_pos (a*a) 998244853 ltac:(nia) ltac:(lia)); lia.
Qed.

Lemma proof_of_modpow_entail_wit_2_2_split_goal_3 : modpow_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (Z.rem_bound_pos (a*a) 998244853 ltac:(nia) ltac:(lia)); lia.
Qed.

Lemma proof_of_modpow_entail_wit_2_2_split_goal_4 : modpow_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite (proj1 (P080_parity_shift__modpow e)).
  apply Z.le_trans with e; [apply Z.div_le_upper_bound; lia | exact PreH2].
Qed.

Lemma proof_of_modpow_entail_wit_2_2_split_goal_5 : modpow_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  apply Z.shiftr_nonneg. exact PreH1.
Qed.

Lemma proof_of_modpow_entail_wit_2_2 : modpow_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modpow_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_modpow_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_modpow_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_modpow_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_modpow_entail_wit_2_2_split_goal_5.
Qed. 

Lemma proof_of_modpow_return_wit_1_split_goal_1 : modpow_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst e. rewrite Z.pow_0_r, Z.mul_1_r, Z.rem_small in PreH9 by lia. exact PreH9.
Qed.

Lemma proof_of_modpow_return_wit_1 : modpow_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modpow_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH10 (i - 1) ltac:(lia)) as Hr.
  rewrite Z.sub_0_r.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH10 (i - 1) ltac:(lia)) as Hr.
  rewrite Z.sub_0_r.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH13 (i - i) ltac:(lia)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH13 (i - i) ltac:(lia)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_38_split_goal_1 : solver_safety_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH26 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH26 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_2 : solver_safety_wit_38_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH26 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH26 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_44_split_goal_1 : solver_safety_wit_44_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH30 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH30 (x*W+(y-1)) ltac:(lia)) as Hl.
  rewrite Znth_replace_Znth_Diff by lia.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_44_split_goal_2 : solver_safety_wit_44_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH30 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH30 (x*W+(y-1)) ltac:(lia)) as Hl.
  rewrite Znth_replace_Znth_Diff by lia.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_44_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_44_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_46_split_goal_1 : solver_safety_wit_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH30 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH30 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_46_split_goal_2 : solver_safety_wit_46_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH30 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH30 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_46_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_46_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_47_split_goal_1 : solver_safety_wit_47_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH28 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH28 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_47_split_goal_2 : solver_safety_wit_47_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH28 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH28 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_47_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_47_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_49_split_goal_1 : solver_safety_wit_49_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH28 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH28 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_49_split_goal_2 : solver_safety_wit_49_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH28 ((x-1)*W+y) ltac:(lia)) as Hu.
  pose proof (PreH28 (x*W+(y-1)) ltac:(lia)) as Hl.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_49_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_49_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_58_split_goal_1 : solver_safety_wit_58_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  pose proof (Z.rem_bound_pos ((Znth (x + y - 1) fl 0) * (Znth y il 0)) 998244853 ltac:(nia) ltac:(lia)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_58_split_goal_2 : solver_safety_wit_58_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  pose proof (Z.rem_bound_pos ((Znth (x + y - 1) fl 0) * (Znth y il 0)) 998244853 ltac:(nia) ltac:(lia)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_58_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_58_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_63_split_goal_1 : solver_safety_wit_63_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_63_split_goal_2 : solver_safety_wit_63_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_63_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_63_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_79_split_goal_1 : solver_safety_wit_79_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  pose proof (Z.rem_bound_pos ((Znth (x + y - 1) fl 0) * (Znth x il 0)) 998244853 ltac:(nia) ltac:(lia)) as Hr.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_79_split_goal_2 : solver_safety_wit_79_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  pose proof (Z.rem_bound_pos ((Znth (x + y - 1) fl 0) * (Znth x il 0)) 998244853 ltac:(nia) ltac:(lia)) as Hr.
  nia.
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
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_84_split_goal_2 : solver_safety_wit_84_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | H : forall j : Z, 0 <= j < ?N + 1 -> (((0 <= Znth j ?fl 0 /\ Znth j ?fl 0 < 998244853) /\ 0 <= Znth j ?il 0) /\ Znth j ?il 0 < 998244853) |- _ =>
      pose proof (H (x + y - 1) ltac:(lia)) as Ha;
      pose proof (H x ltac:(lia)) as Hb;
      pose proof (H y ltac:(lia)) as Hc;
      pose proof (H (x + y - 1 - x) ltac:(lia)) as Hd;
      pose proof (H (x + y - 1 - y) ltac:(lia)) as He
  end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_84_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_84_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_92_split_goal_1 : solver_safety_wit_92_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH30 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH30 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_92_split_goal_2 : solver_safety_wit_92_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH30 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH30 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_92 : solver_safety_wit_92.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_92_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_92_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_94_split_goal_1 : solver_safety_wit_94_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH30 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH30 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_94_split_goal_2 : solver_safety_wit_94_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH30 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH30 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_94 : solver_safety_wit_94.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_94_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_94_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_95_split_goal_1 : solver_safety_wit_95_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH28 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH28 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_95_split_goal_2 : solver_safety_wit_95_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH28 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH28 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_95 : solver_safety_wit_95.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_95_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_95_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_97_split_goal_1 : solver_safety_wit_97_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH28 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH28 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_97_split_goal_2 : solver_safety_wit_97_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH28 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH28 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_97 : solver_safety_wit_97.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_97_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_97_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_106_split_goal_1 : solver_safety_wit_106_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH27 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH27 y ltac:(lia)) as B2.
  pose proof (PreH27 (x+y-1-y) ltac:(lia)) as B3.
  rewrite Z.rem_mod_nonneg by nia.
  pose proof (Z.mod_pos_bound (Znth (x+y-1) fl 0 * Znth y il 0) 998244853 ltac:(lia)) as BM.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_106_split_goal_2 : solver_safety_wit_106_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH27 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH27 y ltac:(lia)) as B2.
  pose proof (PreH27 (x+y-1-y) ltac:(lia)) as B3.
  rewrite Z.rem_mod_nonneg by nia.
  pose proof (Z.mod_pos_bound (Znth (x+y-1) fl 0 * Znth y il 0) 998244853 ltac:(lia)) as BM.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_106 : solver_safety_wit_106.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_106_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_106_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_111_split_goal_1 : solver_safety_wit_111_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH27 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH27 y ltac:(lia)) as B2.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_111_split_goal_2 : solver_safety_wit_111_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH27 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH27 y ltac:(lia)) as B2.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_111 : solver_safety_wit_111.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_111_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_111_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_127_split_goal_1 : solver_safety_wit_127_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH29 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH29 x ltac:(lia)) as B2.
  pose proof (PreH29 (x+y-1-x) ltac:(lia)) as B3.
  rewrite Z.rem_mod_nonneg by nia.
  pose proof (Z.mod_pos_bound (Znth (x+y-1) fl 0 * Znth x il 0) 998244853 ltac:(lia)) as BM.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_127_split_goal_2 : solver_safety_wit_127_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH29 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH29 x ltac:(lia)) as B2.
  pose proof (PreH29 (x+y-1-x) ltac:(lia)) as B3.
  rewrite Z.rem_mod_nonneg by nia.
  pose proof (Z.mod_pos_bound (Znth (x+y-1) fl 0 * Znth x il 0) 998244853 ltac:(lia)) as BM.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_127 : solver_safety_wit_127.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_127_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_127_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_132_split_goal_1 : solver_safety_wit_132_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH29 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH29 x ltac:(lia)) as B2.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_132_split_goal_2 : solver_safety_wit_132_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (PreH29 (x+y-1) ltac:(lia)) as B1.
  pose proof (PreH29 x ltac:(lia)) as B2.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_132 : solver_safety_wit_132.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_132_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_132_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_141_split_goal_1 : solver_safety_wit_141_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_141_split_goal_2 : solver_safety_wit_141_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with |- context [Z.rem ?a 998244853] => let H := fresh "Hmod" in pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as H; let z := fresh "residue" in remember (Z.rem a 998244853) as z in * end.
  repeat rewrite Z.abs_lt in *; cbn [Z.abs] in *.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_141 : solver_safety_wit_141.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_141_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_141_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_147_split_goal_1 : solver_safety_wit_147_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH30 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH30 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_147_split_goal_2 : solver_safety_wit_147_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  repeat match goal with
  | |- context [Z.rem ?a 998244853] =>
    let Hr := fresh "Hr" in
    pose proof (Z.rem_bound_abs a 998244853 ltac:(lia)) as Hr;
    change (Z.abs (Z.rem a 998244853) < 998244853) in Hr;
    apply Z.abs_lt in Hr;
    let r := fresh "r" in remember (Z.rem a 998244853) as r in |- *
  end.
  all: try (pose proof (PreH30 (((x - 1) * W) + y) ltac:(lia)) as Hu;
            pose proof (PreH30 ((x * W) + (y - 1)) ltac:(lia)) as Hl).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_147 : solver_safety_wit_147.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_147_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_147_split_goal_2.
Qed. 

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
LLM_pre_process ltac:(idtac).
Exists (1 :: nil).
split_pure_spatial.
- cancel (Int64Array.undef_seg retval 1 (n_pre + m_pre + 1)).
  cancel (Int64Array.undef_full retval_2 (n_pre + m_pre + 1)).
  apply (Int64Array.seg_single retval 0 1).
- split_pures; dump_pre_spatial; try lia; try reflexivity.
  intros j Hj. assert (j=0) by lia. subst j.
  rewrite P080Factorial_zero. cbn. lia.
Qed. 

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
LLM_pre_process ltac:(idtac).
rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
aggressive_pre_process.
Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hi : i = N+1) by (clear - PreH4 PreH11; lia). rewrite Hi in *.
  Exists (retval :: nil) fl_2.
  split_pure_spatial.
  - unfold Int64Array.full, store_array.
    fold (Int64Array.seg fac 0 (N+1) fl_2).
    sep_apply_l_atomic (Int64Array.seg_single ifac N retval).
    cancel (Int64Array.seg fac 0 (N+1) fl_2).
    cancel (Int64Array.undef_seg ifac 0 N).
    cancel (Int64Array.seg ifac N (N+1) (retval :: nil)).
  - split_pures; dump_pre_spatial; try assumption; try solve [match goal with |- _ <= _ => clear PreH1; lia | |- _ = _ => clear PreH1; lia end].
    + rewrite Zlength_cons, Zlength_nil. clear PreH1. lia.
    + unfold P080Factorials. intros j Hj. specialize (PreH13 j Hj). rewrite P080_factorial_rem__inverse_factorials in PreH13. tauto.
    + unfold P080InverseFactorials. intros j Hj.
      assert (j=N) by (clear - Hj; lia). subst j. replace (N-N) with 0 by ring.
      rewrite Znth0_cons. rewrite PreH1.
      rewrite P080_pow_rem__inverse_factorials.
      2: { replace (N-0) with N by ring. exact (proj2 (proj1 (PreH13 N ltac:(clear - PreH5 PreH6 PreH8; lia)))). }
      replace (N-0) with N by ring.
      rewrite (proj1 (proj1 (PreH13 N ltac:(clear - PreH5 PreH6 PreH8; lia)))).
      rewrite P080_factorial_rem__inverse_factorials.
      apply P080_pow_mod_congruence__inverse_factorials; clear PreH1; lia.
    + intros j Hj. specialize (PreH13 j Hj). tauto.
    + intros j Hj. assert (j=0) by (clear - Hj; lia). subst j. rewrite Znth0_cons. clear PreH1. lia.
Qed. 

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(auto).
  replace (i-i) with 0 by lia.
  rewrite Z.rem_mod_nonneg by (pose proof (PreH13 0 ltac:(lia)); nia).
  Exists (((Znth 0 il_2 0*i) mod 998244853)::il_2) fl_2.
  split_pure_spatial.
  - rewrite (Int64Array.seg_unfold ifac (i-1) (N+1) il_2 ((Znth 0 il_2 0*i) mod 998244853)).
    replace (i-1+1) with i by lia.
    cancel (Int64Array.full fac (N+1) fl_2).
    cancel (Int64Array.undef_seg ifac 0 (i-1)).
    cancel (Int64Array.seg ifac i (N+1) il_2).
    cancel ((ifac+(i-1)*sizeof(INT64)) # Int64 |-> ((Znth 0 il_2 0*i) mod 998244853)).
  - split_pures; dump_pre_spatial; try assumption; try solve [match goal with |- _ <= _ => lia | |- _ = _ => lia end].
    + rewrite Zlength_cons. lia.
    + unfold P080InverseFactorials in *. intros j Hj.
      destruct (Z.eq_dec j (i-1)) as [-> | Hneq].
      * replace (i-1-(i-1)) with 0 by lia. rewrite Znth0_cons.
        specialize (PreH11 i ltac:(lia)).
        replace (i-i) with 0 in PreH11 by ring. rewrite PreH11.
        apply P080_inverse_down__inverse_factorials. clear PreH11. lia.
      * rewrite Znth_cons by lia.
        replace (j-(i-1)-1) with (j-i) by lia. apply PreH11. lia.
    + intros j Hj. destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Znth0_cons. apply Z.mod_pos_bound. lia.
      * rewrite Znth_cons by lia. apply PreH13. lia.
Qed. 

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
LLM_pre_process ltac:(idtac).
subst i.
Exists (repeat_Z 0 ((n_pre+1)*(m_pre+1))) (repeat_Z 0 ((n_pre+1)*(m_pre+1))) il_2 fl_2.
split_pure_spatial.
- unfold Int64Array.full, Int64Array.seg, store_array. cancel.
- split_pures; dump_pre_spatial; try lia; try assumption.
  all: try (unfold repeat_Z; rewrite Zlength_correct, repeat_length, Z2Nat.id by nia; reflexivity).
  all: intros j Hj.
  all: try (specialize (PreH14 j Hj); specialize (PreH15 j ltac:(lia)); tauto).
  all: try (unfold repeat_Z, Znth; rewrite nth_repeat; lia).
Qed. 

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
LLM_pre_process ltac:(idtac).
rewrite Zlength_replace_Znth. rewrite <- PreH3. exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
aggressive_pre_process.
Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Ey : y = m_pre + 1) by lia.
  unfold P080Tables. intros r c Hr Hc.
  assert (EW : W = m_pre + 1) by lia.
  assert (B : 0 <= r * (m_pre + 1) + c < (n_pre + 1) * W).
  { rewrite EW. apply P080_flat_bounds__table_boundaries; assumption. }
  split.
  - intros E. assert (Er : r = 0) by lia. subst r.
    replace (0 * (m_pre + 1) + c) with c by ring.
    rewrite PreH18 by lia. rewrite PreH20 by nia.
    pose proof (P080_spec_boundaries__table_boundaries c ltac:(lia)) as [Hs [Hk _]]. split; [symmetry; exact Hk|exact Hs].
  - intros E. split; [apply PreH19|apply PreH20]; nia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  apply PreH15; assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  apply PreH14; assumption.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  intros r c Hr Hc.
  assert (B : 0 <= r * (m_pre + 1) + c < Zlength dl_2).
  { rewrite PreH17, PreH9. apply P080_flat_bounds__table_boundaries; assumption. }
  assert (Bx : 0 <= x * (m_pre + 1) + 0 < Zlength dl_2).
  { rewrite PreH17, PreH9. apply P080_flat_bounds__table_boundaries; lia. }
  specialize (PreH24 r c Hr Hc). destruct PreH24 as [Old Future].
  destruct (Z.eq_dec (r * (m_pre + 1) + c) (x * (m_pre + 1) + 0)) as [E|E].
  - pose proof (P080_flat_index_injective__table_boundaries m_pre r c x 0 PreH12 Hc ltac:(lia) E) as [Er Ec]. subst r c.
    split.
    + intros _. rewrite Znth_replace_Znth_Same by assumption.
      specialize (Future ltac:(right; split; lia)).
      pose proof (P080_spec_boundaries__table_boundaries x ltac:(lia)) as H.
      destruct Future as [K0 D0]. rewrite K0. split; [symmetry; apply H; lia|tauto].
    + intros F. lia.
  - rewrite Znth_replace_Znth_Diff by (try assumption; lia).
    split.
    + intros F. apply Old. destruct F as [F|[F G]]; [auto|].
      assert (c=0) by lia. subst r c. contradiction.
    + intros F. apply Future. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  destruct (Z.eq_dec j_2 (x * W + 0)) as [E|E].
  - subst j_2. rewrite Znth_replace_Znth_Same by lia.
    specialize (PreH21 (x * W + 0) ltac:(lia)). lia.
  - rewrite Znth_replace_Znth_Diff by lia. apply PreH21. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  apply PreH20; assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Zlength_replace_Znth, PreH17, PreH9. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
Qed. 

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_2 : solver_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_3 : solver_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_10_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_10_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst W N.
  match goal with H : P080Tables _ _ _ _ _ _ |- _ => pose proof H as HT end.
  destruct (HT (x-1) y ltac:(lia) ltac:(lia)) as [Hup _].
  specialize (Hup ltac:(left; lia)). destruct Hup as [HKup HDup].
  destruct (HT x (y-1) ltac:(lia) ltac:(lia)) as [Hleft _].
  specialize (Hleft ltac:(right; split; lia)). destruct Hleft as [HKleft HDleft].
  rewrite Znth_replace_Znth_Diff by nia.
  replace (x+y-1-y) with (x-1) by lia.
  replace (x+y-1-x) with (y-1) by lia.
  eapply P080_table_step__dp_semantics; try eassumption; try lia.
  - rewrite HKup, HKleft.
    pose proof (P080ZeroCount_range (x-1) y).
    pose proof (P080ZeroCount_range x (y-1)).
    rewrite Z.rem_mod_nonneg by lia.
    symmetry. apply P080_zero_count_recurrence__dp_semantics; lia.
  - eapply P080_cell_value__dp_semantics with (N:=n_pre+m_pre); try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_2 : solver_entail_wit_11_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Zlength_replace_Znth. nia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_3 : solver_entail_wit_11_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Zlength_replace_Znth. nia.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst W N.
  match goal with H : P080Tables _ _ _ _ _ _ |- _ => pose proof H as HT end.
  destruct (HT (x-1) y ltac:(lia) ltac:(lia)) as [Hup _].
  specialize (Hup ltac:(left; lia)). destruct Hup as [HKup HDup].
  destruct (HT x (y-1) ltac:(lia) ltac:(lia)) as [Hleft _].
  specialize (Hleft ltac:(right; split; lia)). destruct Hleft as [HKleft HDleft].
  destruct (HT x y ltac:(lia) ltac:(lia)) as [_ Hcur].
  specialize (Hcur ltac:(right; split; lia)). destruct Hcur as [HKcur HDcur].
  replace (x+y-1-y) with (x-1) by lia.
  replace (x+y-1-x) with (y-1) by lia.
  eapply P080_table_step_D__dp_semantics; try eassumption; try lia.
  - rewrite P080_zero_count_impossible__dp_semantics by lia. exact HKcur.
  - eapply P080_cell_value__dp_semantics with (N:=n_pre+m_pre); try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_2 : solver_entail_wit_11_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Zlength_replace_Znth. nia.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_2.
Qed. 

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold P080Tables in *.
  intros r c Hr Hc.
  specialize (PreH20 r c Hr Hc).
  destruct PreH20 as [Hdone Hfuture].
  split; intros Hfront.
  - apply Hdone. lia.
  - apply Hfuture. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH15. assumption.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH14. assumption.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
Qed. 

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hx : x = n_pre + 1) by lia.
  subst x. eapply P080Tables_exit; eauto.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_1 : solver_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH16 ((n_pre + m_pre) - 0) ltac:(lia)) as Hr.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_2 : solver_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH16 ((n_pre + m_pre) - 0) ltac:(lia)) as Hr.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_3 : solver_partial_solve_wit_7_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH16 ((n_pre + m_pre) - 0) ltac:(lia)) as Hr.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_4 : solver_partial_solve_wit_7_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (PreH16 ((n_pre + m_pre) - 0) ltac:(lia)) as Hr.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_4.
Qed. 

