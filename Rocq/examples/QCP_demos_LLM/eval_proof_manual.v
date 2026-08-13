Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import eval_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.eval_lib.
Local Open Scope sac.

Lemma proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH9.
  assert (Hop: op = T_plus)
    by (destruct op; simpl in PreH9; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH10.
  assert (Hop: op = T_minus)
    by (destruct op; simpl in PreH10; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH11.
  assert (Hop: op = T_mul)
    by (destruct op; simpl in PreH11; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH12.
  assert (Hop: op = T_div)
    by (destruct op; simpl in PreH12; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH13.
  assert (Hop: op = T_mod)
    by (destruct op; simpl in PreH13; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct op; simpl in PreH8; subst v; lia.
Qed.

Lemma proof_of_eval_safety_wit_31 : eval_safety_wit_31.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hop: op = T_uminus).
  { destruct op; simpl in PreH6; subst v; try reflexivity; lia. }
  subst op.
  rewrite PreH5 in PreH3.
  apply safe_eval_un_cond in PreH3.
  unfold un_safe_cond in PreH3.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_32 : eval_safety_wit_32.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct e0; simpl in *; Intro_any; try lia.
  Intro_any. lia.
Qed.

Lemma proof_of_eval_entail_wit_1 : eval_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct e0; simpl.
  - Exists 0.
    split_pure_spatial.
    + cancel (IntArray.full var_value_pre 100 l). repeat cancel.
    + repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
  - Exists 1.
    split_pure_spatial.
    + cancel (IntArray.full var_value_pre 100 l). repeat cancel.
    + repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
  - Intros p. Exists 3 p.
    split_pure_spatial.
    + cancel (IntArray.full var_value_pre 100 l). repeat cancel.
    + repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
  - Intros p1 p2. Exists 2 p1 p2.
    split_pure_spatial.
    + cancel (IntArray.full var_value_pre 100 l). repeat cancel.
    + repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
Qed.

Lemma proof_of_eval_entail_wit_2 : eval_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct e0; simpl.
  - Exists z e_t_2.
    split_pure_spatial.
    + Intros_p Htag. cancel (IntArray.full var_value_pre 100 l). repeat cancel.
    + repeat split_pures.
      all: Intros_p Htag; dump_pre_spatial; try exact PreH1; try reflexivity; try lia.
  - Intros_p Htag. lia.
  - Intros p'. lia.
  - Intros p1 p2. lia.
Qed.

Lemma proof_of_eval_entail_wit_3 : eval_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  destruct e0; simpl.
  - Intros_p Htag. lia.
  - Exists e_t_2 z.
    inversion PreH1; subst.
    split_pure_spatial.
    + Intros_p Htag. repeat cancel.
    + split_pures.
      * dump_pre_spatial; assumption.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; rewrite Zlength_correct in Hlen; lia.
      * dump_pre_spatial; reflexivity.
      * dump_pre_spatial; reflexivity.
  - Intros p'. lia.
  - Intros p1 p2. lia.
Qed.

Lemma proof_of_eval_entail_wit_4 : eval_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst e_t_2.
  destruct e0; simpl.
  - Intros_p Htag. lia.
  - Intros_p Htag. lia.
  - Intros p'. lia.
  - Intros p1 p2.
    Exists p2 p1.
    Exists (BinOpID b) b e0_1 e0_2 2.
    split_pure_spatial.
    + repeat cancel.
    + repeat split_pures; dump_pre_spatial; try exact PreH1; try reflexivity; try lia.
Qed.

Lemma proof_of_eval_entail_wit_5 : eval_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst e_t_2.
  destruct e0; simpl.
  - Intros_p Htag. lia.
  - Intros_p Htag. lia.
  - Intros p'.
    Exists p' (UnOpID u) u e0 3.
    split_pure_spatial.
    + repeat cancel.
    + repeat split_pures; dump_pre_spatial; try exact PreH1; try reflexivity; try lia.
  - Intros p1 p2. lia.
Qed.

Lemma proof_of_eval_return_wit_1 : eval_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  destruct op; simpl in *; try discriminate; try lia.
  simpl store_expr.
  Exists v_2.
  split_pure_spatial.
  - cancel (store_expr v_2 e1). cancel (IntArray.full var_value_pre 100 l). repeat cancel.
  - dump_pre_spatial; lia.
Qed.
Lemma proof_of_eval_return_wit_2 : eval_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  destruct op; simpl in *; try discriminate; try lia.
  simpl store_expr.
  Exists v_2.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct (expr_eval e1 l =? 0)%Z eqn:Heq.
    + apply Z.eqb_eq in Heq. lia.
    + apply Z.eqb_neq in Heq. lia.
Qed.
Lemma proof_of_eval_return_wit_3 : eval_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  destruct op; simpl in *; try discriminate; try lia.
  simpl store_expr.
  Exists v_2.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct (expr_eval e1 l =? 0)%Z eqn:Heq.
    + apply Z.eqb_eq in Heq. lia.
    + apply Z.eqb_neq in Heq. lia.
Qed.
Lemma proof_of_eval_return_wit_4 : eval_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_5 : eval_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_6 : eval_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_7 : eval_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_8 : eval_return_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_9 : eval_return_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_10 : eval_return_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_11 : eval_return_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_12 : eval_return_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_13 : eval_return_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_14 : eval_return_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_15 : eval_return_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_16 : eval_return_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_17 : eval_return_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_18 : eval_return_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_19 : eval_return_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_20 : eval_return_wit_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_21 : eval_return_wit_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - rewrite <- PreH8. repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_22 : eval_return_wit_22.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - rewrite <- PreH8. repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_23 : eval_return_wit_23.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - rewrite <- PreH7. repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_24 : eval_return_wit_24.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - rewrite <- PreH6. repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_25 : eval_return_wit_25.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - rewrite <- PreH7. repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_26 : eval_return_wit_26.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst. simpl.
  Exists v_2 v_3.
  split_pure_spatial.
  - rewrite <- PreH7. repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_27 : eval_return_wit_27.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  split_pure_spatial.
  - cbn. repeat cancel.
  - dump_pre_spatial. reflexivity.
Qed.
Lemma proof_of_eval_return_wit_28 : eval_return_wit_28.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  split_pure_spatial.
  - cbn. repeat cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_eval_partial_solve_wit_2_pure : eval_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
Lemma proof_of_eval_partial_solve_wit_3_pure : eval_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
Lemma proof_of_eval_partial_solve_wit_4_pure : eval_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
Lemma proof_of_eval_partial_solve_wit_5_pure : eval_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
Lemma proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
Lemma proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
Lemma proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_un_arg.
Qed.
Lemma proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_un_arg.
Qed.
