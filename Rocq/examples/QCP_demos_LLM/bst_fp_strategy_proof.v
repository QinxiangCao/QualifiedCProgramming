Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import bst_fp_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import bst_fp_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma bst_fp_strategy0_correctness : bst_fp_strategy0.
Proof.
  pre_process_default.
  Intros_p H.
  subst tr1.
  cancel.
Qed.

Lemma bst_fp_strategy1_correctness : bst_fp_strategy1.
Proof.
  pre_process_default.
  Intros_p H.
  subst pt.
  simpl.
  split_pure_spatial.
  2: {
    split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
  }
  cancel.
Qed.

Lemma bst_fp_strategy2_correctness : bst_fp_strategy2.
Proof.
  pre_process_default.
  cancel.
  Intros_r tr0.
  Intros_r tr1.
  Intros_r v.
  Intros_r tr2.
  Intros_r k.
  Intros_r l.
  Intros_r r.
  apply_sepcon_adjoint.
  pre_process_default.
  subst tr0.
  sep_apply_r_atomic (store_tree_make_tree p k v l r fa tr1 tr2).
  - dump_pre_spatial.
    exact H.
  - dump_pre_spatial.
    split.
    + exact H0.
    + exact H1.
  - cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p # "tree" ->ₛ "left") # Ptr |-> l).
    cancel (&(p # "tree" ->ₛ "right") # Ptr |-> r).
    cancel (&(p # "tree" ->ₛ "father") # Ptr |-> fa).
    cancel (store_tree l p tr1).
    cancel (store_tree r p tr2).
Qed.
