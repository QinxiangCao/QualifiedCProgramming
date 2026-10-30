From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_lib.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma bst_fp_strategy0_correctness : bst_fp_strategy0.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma bst_fp_strategy1_correctness : bst_fp_strategy1.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma bst_fp_strategy2_correctness : bst_fp_strategy2.
  pre_process_default.
  entailer!.
  Intros_r tr0.
  Intros_r tr1.
  Intros_r v.
  Intros_r tr2.
  Intros_r k.
  Intros_r l.
  Intros_r r.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros.
  subst.
  simpl.
  entailer!.
  Exists l r.
  entailer!.
Qed.