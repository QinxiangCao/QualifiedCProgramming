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
From SimpleC.EE.QCP_demos_human Require Import eval_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.eval_lib.
Local Open Scope sac.

Lemma proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e0.
  assert (Hop: op = T_plus)
    by (destruct op; simpl in *; try lia; try discriminate; reflexivity).
  subst op.
  inversion PreH7 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e0.
  assert (Hop: op = T_minus)
    by (destruct op; simpl in *; try lia; try discriminate; reflexivity).
  subst op.
  inversion PreH7 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e0.
  assert (Hop: op = T_mul)
    by (destruct op; simpl in *; try lia; try discriminate; reflexivity).
  subst op.
  inversion PreH7 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e0.
  assert (Hop: op = T_div)
    by (destruct op; simpl in *; try lia; try discriminate; reflexivity).
  subst op.
  inversion PreH7 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e0.
  assert (Hop: op = T_mod)
    by (destruct op; simpl in *; try lia; try discriminate; reflexivity).
  subst op.
  inversion PreH7 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct op; simpl in *; lia.
Qed.

Lemma proof_of_eval_safety_wit_31 : eval_safety_wit_31.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hop: op = T_uminus).
  { destruct op; simpl in *; try reflexivity; lia. }
  subst op.
  subst e0.
  inversion PreH5; subst.
  unfold un_safe_cond in *; simpl in *.
  repeat split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_safety_wit_32 : eval_safety_wit_32.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct e0; simpl in *; Intro_any; try lia.
  Intro_any. lia.
Qed.

Lemma proof_of_eval_return_wit_1 : eval_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct op; simpl in *; try discriminate; try lia.
  simpl store_expr.
  Exists v.
  split_pure_spatial.
  - repeat cancel. 
  - dump_pre_spatial. lia.
Qed.
Lemma proof_of_eval_return_wit_2 : eval_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct op; simpl in *; try discriminate; try lia.
  simpl store_expr.
  Exists v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct (expr_eval e1 l =? 0)%Z eqn:Heq.
    + apply Z.eqb_eq in Heq. lia.
    + apply Z.eqb_neq in Heq. lia.
Qed.
Lemma proof_of_eval_return_wit_3 : eval_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct op; simpl in *; try discriminate; try lia.
  simpl store_expr.
  Exists v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct (expr_eval e1 l =? 0)%Z eqn:Heq.
    + apply Z.eqb_eq in Heq. lia.
    + apply Z.eqb_neq in Heq. lia.
Qed.
Lemma proof_of_eval_return_wit_4 : eval_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH22.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_5 : eval_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH22.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_6 : eval_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH21.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_7 : eval_return_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH21.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_8 : eval_return_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH20.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_9 : eval_return_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH20.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_10 : eval_return_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH19.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_11 : eval_return_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH19.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <=? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_12 : eval_return_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH18.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_13 : eval_return_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH18.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l >? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_14 : eval_return_wit_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH17.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_15 : eval_return_wit_15.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH17.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l <? expr_eval e2 l)%Z eqn:I; lia.
Qed.
Lemma proof_of_eval_return_wit_16 : eval_return_wit_16.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH15.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_17 : eval_return_wit_17.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH14.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_18 : eval_return_wit_18.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite PreH13.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_19 : eval_return_wit_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite PreH12.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_20 : eval_return_wit_20.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite PreH11.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
Qed.
Lemma proof_of_eval_return_wit_21 : eval_return_wit_21.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH6.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_22 : eval_return_wit_22.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH6.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_23 : eval_return_wit_23.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH5.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_24 : eval_return_wit_24.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH4.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
Qed.
Lemma proof_of_eval_return_wit_25 : eval_return_wit_25.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH5.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_26 : eval_return_wit_26.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl.
  rewrite <- PreH5.
  Exists v_2 v.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    destruct op; try discriminate; auto.
    destruct (expr_eval e1 l =? 0)%Z eqn:I; try lia.
    destruct (expr_eval e2 l =? 0)%Z eqn:J; try lia.
Qed.
Lemma proof_of_eval_return_wit_27 : eval_return_wit_27.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cbn. repeat cancel.
  - dump_pre_spatial. reflexivity.
Qed.
Lemma proof_of_eval_return_wit_28 : eval_return_wit_28.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cbn. repeat cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma safe_eval_bin_left: forall op e1 e2 vs,
  safe_eval (EBinop op e1 e2) vs -> safe_eval e1 vs.
Proof.
  intros. inversion H; subst; auto.
Qed.

Lemma safe_eval_bin_right: forall op e1 e2 vs,
  safe_eval (EBinop op e1 e2) vs -> safe_eval e2 vs.
Proof.
  intros. inversion H; subst; auto.
Qed.

Lemma safe_eval_un_arg: forall op e vs,
  safe_eval (EUnop op e) vs -> safe_eval e vs.
Proof.
  intros. inversion H; subst; auto.
Qed.

(* Already exported by eval_proof_auto.v; keep the manual proof commented to avoid
   duplicate labels when eval_goal_check includes auto before manual.
Lemma proof_of_eval_partial_solve_wit_1 : eval_partial_solve_wit_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_eval_partial_solve_wit_2_pure : eval_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
Lemma proof_of_eval_partial_solve_wit_2 : eval_partial_solve_wit_2.
Proof.
  intros _.
  unfold eval_partial_solve_wit_2_aux.
  intros; subst e_t.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
Qed.

Lemma proof_of_eval_partial_solve_wit_3_pure : eval_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
Lemma proof_of_eval_partial_solve_wit_3 : eval_partial_solve_wit_3.
Proof.
  intros _.
  unfold eval_partial_solve_wit_3_aux.
  intros; subst e_t.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
Qed.

Lemma proof_of_eval_partial_solve_wit_4 : eval_partial_solve_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  prop_apply (IntArray.full_length).
  Intros.
  sep_apply (IntArray.full_split_to_missing_i var_value_pre n 100 l 0); [ | tauto].
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try reflexivity; try exact PreH5; lia.
Qed.

Lemma proof_of_eval_partial_solve_wit_5_pure : eval_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
Lemma proof_of_eval_partial_solve_wit_5 : eval_partial_solve_wit_5.
Proof.
  intros _.
  unfold eval_partial_solve_wit_5_aux.
  intros; subst e_t.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_6 : eval_partial_solve_wit_6.
Proof.
  intros _.
  unfold eval_partial_solve_wit_6_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_7 : eval_partial_solve_wit_7.
Proof.
  intros _.
  unfold eval_partial_solve_wit_7_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_8 : eval_partial_solve_wit_8.
Proof.
  intros _.
  unfold eval_partial_solve_wit_8_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_9 : eval_partial_solve_wit_9.
Proof.
  intros _.
  unfold eval_partial_solve_wit_9_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_10_pure : eval_partial_solve_wit_10_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_10 : eval_partial_solve_wit_10.
Proof.
  intros _.
  unfold eval_partial_solve_wit_10_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_bin_left.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_11_pure : eval_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_11 : eval_partial_solve_wit_11.
Proof.
  intros _.
  unfold eval_partial_solve_wit_11_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_bin_right.
Qed.
*)

(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_12_pure : eval_partial_solve_wit_12_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
Lemma proof_of_eval_partial_solve_wit_12 : eval_partial_solve_wit_12.
Proof.
  intros _.
  unfold eval_partial_solve_wit_12_aux.
  intros; subst e_t.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try exact PreH1; lia.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_13_pure : eval_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_un_arg.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_13 : eval_partial_solve_wit_13.
Proof.
  intros _.
  unfold eval_partial_solve_wit_13_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_un_arg.
Qed.
*)

Lemma proof_of_eval_partial_solve_wit_14_pure : eval_partial_solve_wit_14_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial; subst; eauto using safe_eval_un_arg.
Qed.
(* Already exported by eval_proof_auto.v.
Lemma proof_of_eval_partial_solve_wit_14 : eval_partial_solve_wit_14.
Proof.
  intros _.
  unfold eval_partial_solve_wit_14_aux.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; subst; eauto using safe_eval_un_arg.
Qed.
*)

Lemma proof_of_eval_which_implies_wit_1 : eval_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct e0; simpl.
  + Exists 0.
    split_pure_spatial.
    - repeat cancel.
    - dump_pre_spatial; lia.
  + Exists 1.
    split_pure_spatial.
    - repeat cancel.
    - dump_pre_spatial; lia.
  + Intros p. Exists 3 p.
    split_pure_spatial.
    - repeat cancel.
    - dump_pre_spatial; lia.
  + Intros p1 p2. Exists 2 p1 p2.
    split_pure_spatial.
    - repeat cancel.
    - dump_pre_spatial; lia.
Qed.

Lemma proof_of_eval_which_implies_wit_2 : eval_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e_t.
  unfold store_expr_aux.
  destruct e0; simpl.
  4: { Intros p1 p2. discriminate. }
  3: { Intros p. discriminate. }
  2: { Intros. discriminate. }
  Exists z.
  split_pure_spatial.
  - Intros_p Htag. repeat cancel.
  - repeat split_pures; Intros_p Htag; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_eval_which_implies_wit_3 : eval_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  subst e_t.
  unfold store_expr_aux.
  destruct e0; simpl.
  4: { Intros p1 p2. discriminate. }
  3: { Intros p. discriminate. }
  1: { Intros. discriminate. }
  Exists z. inversion PreH2; subst.
  split_pure_spatial.
  - Intros_p Htag. Intros_p Hone. repeat cancel.
  - repeat split_pures.
    all: Intros_p Hone; dump_pre_spatial; try reflexivity; try lia.
Qed.

Lemma proof_of_eval_which_implies_wit_4 : eval_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e_t.
  unfold store_expr_aux.
  destruct e0; simpl.
  { Intros. discriminate. }
  { Intros. discriminate. }
  { Intros p. discriminate. }
  Intros p1 p2.
  Exists p2 p1 (BinOpID b) b e0_1 e0_2.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; try reflexivity; try lia.
Qed.

Lemma proof_of_eval_which_implies_wit_5 : eval_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst e_t.
  unfold store_expr_aux.
  destruct e0; simpl.
  { Intros. discriminate. }
  { Intros. discriminate. }
  2: { Intros p1 p2. discriminate. }
  Intros p.
  Exists p (UnOpID u) u e0.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; try reflexivity; try lia.
Qed.
