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
From SimpleC.EE.Applications_human.alpha_equiv Require Import alpha_equiv_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.Applications_human.alpha_equiv Require Import ast_lib.
From SimpleC.EE.Applications_human Require Import malloc.
From SimpleC.EE.Applications_human Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_alpha_equiv_safety_wit_16 : alpha_equiv_safety_wit_16.
Proof. 
  LLM_pre_process ltac:(int_auto).
  unfold termtypeID in *.
  destruct term1; lia.
Qed.

Lemma proof_of_alpha_equiv_return_wit_15 : alpha_equiv_return_wit_15.
Proof. 
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  apply store_null_right.
Qed.

Lemma proof_of_alpha_equiv_return_wit_14 : alpha_equiv_return_wit_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  apply store_null_left.
Qed.

Lemma proof_of_alpha_equiv_return_wit_13 : alpha_equiv_return_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - pose proof (store_term_fold_out t2_pre term2 PreH3) as Hfold2.
    sep_apply Hfold2.
    pose proof (store_term_fold_out t1_pre term1 PreH2) as Hfold1.
    sep_apply Hfold1.
    cancel.
  - split_pures; dump_pre_spatial.
    destruct term1; destruct term2; simpl in PreH1; try lia.
    all: unfold term_alpha_eqn, term_alpha_eq; reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_12 : alpha_equiv_return_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1 in PreH2.
  unfold list_Z_cmp in PreH2.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ | discriminate ].
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite PreH5, PreH6.
  Exists y z.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> z).
    cancel (store_string z str2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y).
    cancel (store_string y str1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermVar str1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermVar str2)).
  - split_pures; dump_pre_spatial; auto.
    rewrite Heq.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_11 : alpha_equiv_return_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold list_Z_cmp in PreH2.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ subst retval; contradiction | ].
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite PreH5, PreH6.
  Exists y z.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> z).
    cancel (store_string z str2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y).
    cancel (store_string y str1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermVar str1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermVar str2)).
  - split_pures; dump_pre_spatial; auto.
    rewrite Heq.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite PreH4, PreH5.
  split_pure_spatial.
  - cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ1 con1)).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con1).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ2 con2)).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con2).
  - split_pures; dump_pre_spatial; auto.
    destruct (ctID typ1 =? ctID typ2)%Z eqn:E.
    + apply Z.eqb_eq in E.
      contradiction.
    + reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_9 : alpha_equiv_return_wit_9.
Proof. 
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH6, PreH7.
  split_pure_spatial.
  - cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ1 con1)).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con1).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ2 con2)).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con2).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn, term_alpha_eq.
    rewrite PreH3 at 1.
    rewrite Z.eqb_refl.
    rewrite PreH1.
    rewrite Z.eqb_refl.
    rewrite PreH2.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_8 : alpha_equiv_return_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH6, PreH7.
  split_pure_spatial.
  - cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ1 con1)).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con1).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ2 con2)).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con2).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn, term_alpha_eq.
    rewrite PreH3 at 1.
    rewrite Z.eqb_refl.
    destruct (con1 =? con2)%Z eqn:E.
    + apply Z.eqb_eq in E.
      congruence.
    + rewrite PreH2.
      reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH5, PreH6.
  split_pure_spatial.
  - cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ1 con1)).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con1).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst typ2 con2)).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con2).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn, term_alpha_eq.
    rewrite PreH2 at 1.
    rewrite Z.eqb_refl.
    destruct (con1 =? con2)%Z eqn:E.
    + unfold negb.
      destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
      apply Z.eqb_eq in E, Eq.
      contradiction.
    + unfold negb.
      apply Z.eqb_neq in E.
      destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
      apply Z.eqb_eq in Eq.
      contradiction.
Qed.  

Lemma proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH7, PreH8.
  fold store_term.
  Exists y1 z1 y2 z2.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z2).
    cancel (store_term y2 lt2).
    cancel (store_term z2 rt2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z1).
    cancel (store_term y1 lt1).
    cancel (store_term z1 rt1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt1 rt1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt2 rt2)).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn in *.
    unfold term_alpha_eq.
    fold term_alpha_eq.
    destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | reflexivity].
    destruct (term_alpha_eq rt1 rt2) eqn:Eqr; [ | reflexivity].
    lia.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5 : alpha_equiv_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH7, PreH8.
  fold store_term.
  Exists y1 z1 y2 z2.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z2).
    cancel (store_term y2 lt2).
    cancel (store_term z2 rt2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z1).
    cancel (store_term y1 lt1).
    cancel (store_term z1 rt1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt1 rt1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt2 rt2)).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn in *.
    unfold term_alpha_eq.
    fold term_alpha_eq.
    destruct (term_alpha_eq rt1 rt2) eqn:Eqr; [ | contradiction].
    destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | contradiction].
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH5, PreH6.
  fold store_term.
  Exists y1 z1 y2 z2.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z2).
    cancel (store_term y2 lt2).
    cancel (store_term z2 rt2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z1).
    cancel (store_term y1 lt1).
    cancel (store_term z1 rt1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt1 rt1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt2 rt2)).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn in *.
    unfold term_alpha_eq.
    fold term_alpha_eq.
    destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ simpl in PreH2; lia | reflexivity].
Qed.

Lemma proof_of_alpha_equiv_return_wit_3 : alpha_equiv_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH4, PreH5.
  fold store_term.
  Exists y1 z1 y2 z2.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z2).
    cancel (store_string y2 qv2).
    cancel (store_term z2 qterm2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z1).
    cancel (store_string y1 qv1).
    cancel (store_term z1 qterm1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt1 qv1 qterm1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt2 qv2 qterm2)).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn in *.
    unfold term_alpha_eq.
    fold term_alpha_eq.
    destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in Eq.
    congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH7, PreH8.
  fold store_term.
  Exists y1 z1 y2 z2.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z2).
    cancel (store_string y2 qv2).
    cancel (store_term z2 qterm2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z1).
    cancel (store_string y1 qv1).
    cancel (store_term z1 qterm1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt1 qv1 qterm1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt2 qv2 qterm2)).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn in *.
    unfold term_alpha_eq.
    fold term_alpha_eq.
    rewrite PreH2 in PreH3. 
    unfold list_Z_cmp in PreH3.
    destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
    + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
      pose proof list_Z_eqb2eq qv1 qv2 vEq as vvEq.
      pose proof (term_subst_v_same_name qv1 qv2 qterm2 vvEq) as qtEq.
      rewrite qtEq.
      tauto.
    + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
      rewrite Z.eqb_neq in Eq.
      congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1 : alpha_equiv_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_term.
  rewrite PreH11, PreH12.
  fold store_term.
  Exists y1 z1 y2 z2.
  split_pure_spatial.
  - cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y2).
    cancel (&( t2_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z2).
    cancel (store_string y2 qv2).
    cancel (store_term z2 qterm2).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y1).
    cancel (&( t1_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z1).
    cancel (store_string y1 qv1).
    cancel (store_term z1 qterm1).
    cancel (&( t1_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt1 qv1 qterm1)).
    cancel (&( t2_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt2 qv2 qterm2)).
  - split_pures; dump_pre_spatial; auto.
    unfold term_alpha_eqn in *.
    unfold term_alpha_eq.
    fold term_alpha_eq.
    destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
    + auto.
    + rewrite Z.eqb_neq in Eq.
      congruence.
Qed.


Lemma proof_of_alpha_equiv_which_implies_wit_1_split_goal_1 : alpha_equiv_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_term_unfold t2 term2).
  unfold NULL in *.
  Intros_p Ht2.
  dump_pre_spatial.
  exact Ht2.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_1_split_goal_2 : alpha_equiv_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_term_unfold t1 term1).
  unfold NULL in *.
  Intros_p Ht1.
  dump_pre_spatial.
  exact Ht1.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_1_split_goal_spatial : alpha_equiv_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_term_unfold t1 term1).
  sep_apply (store_term_unfold t2 term2).
  unfold NULL.
  Intros_p Ht1.
  Intros_p Ht2.
  cancel (&( t1 # "term" ->ₛ "type") # Int |-> termtypeID term1).
  cancel (&( t2 # "term" ->ₛ "type") # Int |-> termtypeID term2).
  cancel (store_term' t1 term1).
  cancel (store_term' t2 term2).
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_alpha_equiv_which_implies_wit_1_split_goal_spatial term2 term1 t1 t2).
    cancel.
  - exact (proof_of_alpha_equiv_which_implies_wit_1_split_goal_1 term2 term1 t1 t2).
  - exact (proof_of_alpha_equiv_which_implies_wit_1_split_goal_2 term2 term1 t1 t2).
Qed.
   Lemma proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Proof. 
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Var; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros v1 y1.
  sep_apply store_term'_Var; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros v2 y2.
  Exists y2 y1 v2 v1.
  split_pure_spatial.
  - cancel (&( t1 # "term" ->ₛ "type") # Int |-> termtypeID term1).
    cancel (&( t2 # "term" ->ₛ "type") # Int |-> termtypeID term2).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y1).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y2).
    cancel (store_string y1 v1).
    cancel (store_string y2 v2).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.  

Lemma proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Proof. 
  LLM_pre_process ltac:(int_auto). 
  sep_apply store_term'_Const; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros ty1 c1.
  sep_apply store_term'_Const; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros ty2 c2.
  Exists ty2 c2 ty1 c1.
  split_pure_spatial.
  - cancel (&( t1 # "term" ->ₛ "type") # Int |-> termtypeID term1).
    cancel (&( t2 # "term" ->ₛ "type") # Int |-> termtypeID term2).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ty1).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> c1).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ty2).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> c2).
  - split_pures; dump_pre_spatial; auto; try lia.
  all: try solve [assumption | lia].
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Proof. 
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Apply; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros ltt1 rtt1 yy1 zz1.
  sep_apply store_term'_Apply; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros ltt2 rtt2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists ltt2 rtt2 ltt1 rtt1.
  split_pure_spatial.
  - cancel (&( t1 # "term" ->ₛ "type") # Int |-> termtypeID term1).
    cancel (&( t2 # "term" ->ₛ "type") # Int |-> termtypeID term2).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> yy1).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> zz1).
    cancel (store_term yy1 ltt1).
    cancel (store_term zz1 rtt1).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> yy2).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> zz2).
    cancel (store_term yy2 ltt2).
    cancel (store_term zz2 rtt2).
  - split_pures; dump_pre_spatial; auto; try lia.
  all: try solve [assumption | lia].
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Proof.  
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Quant; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros qtt1 qvv1 bb1 yy1 zz1.
  sep_apply store_term'_Quant; [ | tauto | unfold NULL in *; lia]; unfold NULL.
  Intros qtt2 qvv2 bb2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists qtt2 qvv2 bb2.
  Exists qtt1 qvv1 bb1.
  split_pure_spatial.
  - cancel (&( t1 # "term" ->ₛ "type") # Int |-> termtypeID term1).
    cancel (&( t2 # "term" ->ₛ "type") # Int |-> termtypeID term2).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtt1).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> yy1).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> zz1).
    cancel (store_string yy1 qvv1).
    cancel (store_term zz1 bb1).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtt2).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> yy2).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> zz2).
    cancel (store_string yy2 qvv2).
    cancel (store_term zz2 bb2).
  - split_pures; dump_pre_spatial; auto; try lia.
  all: try solve [assumption | lia].
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.
Proof. 
  LLM_pre_process ltac:(int_auto).
  unfold store_string.
  unfold NULL.
  Intros x n.
  Exists x n.
  split_pure_spatial.
  - cancel (CharArray.full v_2 (Zlength (qv2 ++ all_zero_list n))
        (qv2 ++ all_zero_list n)).
    cancel (CharArray.full v (Zlength (qv1 ++ all_zero_list x))
        (qv1 ++ all_zero_list x)).
    cancel (&( t1 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> v).
    cancel (&( t2 # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> v_2).
  - split_pures; dump_pre_spatial; auto.
Qed.
