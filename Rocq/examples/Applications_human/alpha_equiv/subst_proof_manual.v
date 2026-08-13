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
From SimpleC.EE.Applications_human.alpha_equiv Require Import subst_goal.
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

Lemma proof_of_subst_var_safety_wit_5 : subst_var_safety_wit_5.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold termtypeID in *.
    destruct trm; lia.
Qed.

Lemma proof_of_subst_var_return_wit_6_split_goal_spatial :
    subst_var_return_wit_6_split_goal_spatial.
Proof.    
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH5.
    rewrite PreH16 in PreH5.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_v.
    rewrite PreH7, Heq.
    unfold store_term.
    simpl.
    Exists y z.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 3).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z).
      cancel (store_string y qvar).
      cancel (store_term z qterm).
      cancel (store_string den_pre den_str).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_return_wit_6 : subst_var_return_wit_6.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_return_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_subst_var_return_wit_5_split_goal_spatial :
    subst_var_return_wit_5_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH6.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ rewrite PreH6 in PreH17; contradiction | ].
    unfold term_subst_v.
    rewrite PreH8, Heq.
    unfold store_term.
    simpl.
    rewrite PreH5 in *.
    Exists y z.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 3).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z).
      cancel (store_string y qvar).
      cancel (store_term z (term_subst_v den_str src_str qterm)).
      cancel (store_string den_pre den_str).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_return_wit_5 : subst_var_return_wit_5.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_subst_var_return_wit_4_split_goal_spatial :
    subst_var_return_wit_4_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold term_subst_v.
    rewrite PreH4.
    rewrite PreH6.
    unfold store_term.
    simpl.
    rewrite PreH3 in *.
    Exists y z.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
      cancel (store_term y (term_subst_v den_str src_str lt)).
      cancel (store_term z (term_subst_v den_str src_str rt)).
      cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 2).
      cancel (store_string den_pre den_str).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_return_wit_4 : subst_var_return_wit_4.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_return_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_subst_var_return_wit_3_split_goal_spatial :
  subst_var_return_wit_3_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    subst trm.
    unfold term_subst_v.
    unfold store_term.
    simpl.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 1).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con).
      cancel (store_string den_pre den_str).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_return_wit_3 : subst_var_return_wit_3.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_subst_var_return_wit_2_split_goal_spatial :
    subst_var_return_wit_2_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH4.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ simpl in PreH4; congruence | ].
    unfold term_subst_v.
    rewrite PreH6, Heq.
    unfold store_term.
    simpl.
    fold term_subst_v.
    fold store_term.
    Exists y.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y).
      cancel (store_string y var).
      cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 0).
      cancel (store_string den_pre den_str).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_return_wit_2 : subst_var_return_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_subst_var_return_wit_1_split_goal_spatial :
    subst_var_return_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH5.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ | simpl in PreH5; lia ].
    unfold term_subst_v.
    rewrite PreH7, Heq.
    unfold store_term.
    simpl.
    fold store_term.
    Exists retval_2.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> retval_2).
      cancel (store_string retval_2 den_str).
      cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 0).
      cancel (store_string den_pre den_str).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_return_wit_1 : subst_var_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_return_wit_1_split_goal_spatial.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_4_pure_split_goal_1 :
  subst_var_partial_solve_wit_4_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n1 n2 n3.
    dump_pre_spatial.
    assumption.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_4_pure : subst_var_partial_solve_wit_4_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_partial_solve_wit_4_pure_split_goal_1.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_8_pure_split_goal_1 :
  subst_var_partial_solve_wit_8_pure_split_goal_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n1 n2.
    sep_apply store_term_unfold.
    Intros_p Hy.
    unfold NULL in Hy.
    split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_8_pure : subst_var_partial_solve_wit_8_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_partial_solve_wit_8_pure_split_goal_1.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_9_pure_split_goal_1 :
  subst_var_partial_solve_wit_9_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n1 n2.
    sep_apply store_term_unfold.
    Intros_p Hz.
    unfold NULL in Hz.
    split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_9_pure : subst_var_partial_solve_wit_9_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_partial_solve_wit_9_pure_split_goal_1.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_12_pure_split_goal_1 :
  subst_var_partial_solve_wit_12_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n1 n2 n3.
    sep_apply (store_term_unfold z qterm).
    Intros_p Hz.
    unfold NULL in Hz.
    split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_12_pure : subst_var_partial_solve_wit_12_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_var_partial_solve_wit_12_pure_split_goal_1.
Qed.

Lemma proof_of_subst_var_which_implies_wit_1 : subst_var_which_implies_wit_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term_unfold.
    Intros_p Ht.
    unfold NULL in Ht.
    split_pure_spatial.
    - cancel.
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_which_implies_wit_2 : subst_var_which_implies_wit_2.
Proof.
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Var; [ | tauto | tauto].
    Intros var y.
    Exists y var.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y).
      cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
      cancel (store_string y var).
    - split_pures; dump_pre_spatial; try assumption.
Qed. 

Lemma proof_of_subst_var_which_implies_wit_3 : subst_var_which_implies_wit_3.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Const; [ | tauto | tauto].
    Intros y z.
    Exists y z.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID y).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> z).
      cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
    - split_pures; dump_pre_spatial; try assumption.
Qed. 

Lemma proof_of_subst_var_which_implies_wit_4 : subst_var_which_implies_wit_4.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Apply; [ | tauto | tauto].
    Intros lt rt y z.
    Exists z y lt rt.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
      cancel (store_term y lt).
      cancel (store_term z rt).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_var_which_implies_wit_5 : subst_var_which_implies_wit_5.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Quant; [ | tauto | tauto].
    Intros typ v b y z.
    Exists z y typ v b.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID typ).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z).
      cancel (store_string y v).
      cancel (store_term z b).
    - split_pures; dump_pre_spatial; try assumption.
Qed. 

Lemma proof_of_subst_term_safety_wit_5 : subst_term_safety_wit_5.
Proof. 
    LLM_pre_process ltac:(int_auto). 
    unfold termtypeID in *.
    destruct trm; lia.
Qed.

Lemma proof_of_subst_term_return_wit_6_split_goal_spatial :
    subst_term_return_wit_6_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH5.
    destruct (list_Z_eqb qvar src_str) eqn:Heq.
    -
      unfold term_subst_t.
      rewrite PreH7, Heq.
      unfold store_term.
      simpl.
      Exists y z.
      split_pure_spatial.
      + cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt).
        cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y).
        cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z).
        cancel (store_string y qvar).
        cancel (store_term z qterm).
        cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 3).
        cancel (store_term den_pre den_term).
        cancel (store_string src_pre src_str).
      + split_pures; dump_pre_spatial; try assumption.
    - simpl in PreH5.
      lia.
Qed.

Lemma proof_of_subst_term_return_wit_6 : subst_term_return_wit_6.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_return_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_subst_term_return_wit_5_split_goal_spatial :
    subst_term_return_wit_5_split_goal_spatial.
Proof.  
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH5.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ simpl in PreH5; lia | ].
    unfold term_subst_t.
    rewrite PreH7, Heq.
    unfold store_term.
    simpl.
    Exists y retval_2.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> retval_2).
      cancel (store_string y qvar).
      cancel (store_term retval_2 (term_subst_t den_term src_str qterm)).
      cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 3).
      cancel (store_term den_pre den_term).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_return_wit_5 : subst_term_return_wit_5.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_subst_term_return_wit_4_split_goal_spatial :
  subst_term_return_wit_4_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    subst trm.
    unfold term_subst_t.
    unfold store_term.
    simpl.
    Exists retval retval_2.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> retval).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> retval_2).
      cancel (store_term retval (term_subst_t den_term src_str lt)).
      cancel (store_term retval_2 (term_subst_t den_term src_str rt)).
      cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 2).
      cancel (store_term den_pre den_term).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_return_wit_4 : subst_term_return_wit_4.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_return_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_subst_term_return_wit_3_split_goal_spatial :
  subst_term_return_wit_3_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    subst trm.
    unfold term_subst_t.
    unfold store_term.
    simpl.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 1).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID typ).
      cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> con).
      cancel (store_term den_pre den_term).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_return_wit_3 : subst_term_return_wit_3.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_subst_term_return_wit_2_split_goal_spatial :
    subst_term_return_wit_2_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH4.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ simpl in PreH4; congruence | ].
    unfold term_subst_t.
    rewrite PreH6, Heq.
    unfold store_term.
    simpl.
    fold term_subst_t.
    fold store_term.
    Exists y.
    split_pure_spatial.
    - cancel (&( t_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y).
      cancel (store_string y var).
      cancel (&( t_pre # "term" ->ₛ "type") # Int |-> 0).
      cancel (store_term den_pre den_term).
      cancel (store_string src_pre src_str).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_return_wit_2 : subst_term_return_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_subst_term_return_wit_1_split_goal_spatial :
    subst_term_return_wit_1_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold list_Z_cmp in PreH3.
    rewrite PreH2 in PreH3.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_t.
    rewrite PreH5, Heq.
    unfold store_term.
    simpl.
    fold store_term.
    cancel.
Qed.

Lemma proof_of_subst_term_return_wit_1 : subst_term_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_9_pure_split_goal_1 :
  subst_term_partial_solve_wit_9_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n.
    sep_apply (store_term_unfold y lt).
    Intros_p Hy.
    split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_9_pure : subst_term_partial_solve_wit_9_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_partial_solve_wit_9_pure_split_goal_1.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_10_pure_split_goal_1 :
  subst_term_partial_solve_wit_10_pure_split_goal_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n.
    sep_apply (store_term_unfold z rt).
    Intros_p Hz.
    unfold NULL in Hz.
    split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_10_pure : subst_term_partial_solve_wit_10_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_partial_solve_wit_10_pure_split_goal_1.
Qed. 

Lemma proof_of_subst_term_partial_solve_wit_13_pure_split_goal_1 :
  subst_term_partial_solve_wit_13_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_string.
    Intros n1 n2.
    sep_apply (store_term_unfold z qterm).
    Intros_p Hz.
    unfold NULL in Hz.
    split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_13_pure : subst_term_partial_solve_wit_13_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_subst_term_partial_solve_wit_13_pure_split_goal_1.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_1_split_goal_1 :
  subst_term_which_implies_wit_1_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term_unfold.
    Intros_p Ht.
    dump_pre_spatial.
    exact Ht.
Qed.

Lemma proof_of_subst_term_which_implies_wit_1_split_goal_spatial :
  subst_term_which_implies_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term_unfold.
    Intros_p Ht.
    cancel.
Qed.

Lemma proof_of_subst_term_which_implies_wit_1 : subst_term_which_implies_wit_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term_unfold.
    Intros_p Ht.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial.
      exact Ht.
Qed.

Lemma proof_of_subst_term_which_implies_wit_2 : subst_term_which_implies_wit_2.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Var; [ | tauto | tauto].
    Intros var y.
    Exists y var.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y).
      cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
      cancel (store_string y var).
    - split_pures; dump_pre_spatial; try assumption.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_3 : subst_term_which_implies_wit_3.
Proof. 
    LLM_pre_process ltac:(int_auto).
    rewrite PreH2.
    unfold store_term.
    Exists y.
    split_pure_spatial.
    - cancel.
    - split_pures; dump_pre_spatial; try assumption; reflexivity.
Qed.

Lemma proof_of_subst_term_which_implies_wit_4 : subst_term_which_implies_wit_4.
Proof.
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Const; [ | tauto | tauto].
    Intros y z.
    Exists y z.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID y).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> z).
      cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
    - split_pures; dump_pre_spatial; try assumption.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_5 : subst_term_which_implies_wit_5.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Apply; [ | tauto | tauto].
    Intros lt rt y z.
    Exists z y lt rt.
    split_pure_spatial.
    - cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
      cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
      cancel (store_term y lt).
      cancel (store_term z rt).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_subst_term_which_implies_wit_6 : subst_term_which_implies_wit_6.
Proof. 
    LLM_pre_process ltac:(int_auto).
    sep_apply store_term'_Quant; [ | tauto | tauto].
    Intros typ v b y z.
    Exists z y typ v b.
    split_pure_spatial; [
      cancel (&( t # "term" ->ₛ "type") # Int |-> termtypeID trm);
      cancel (&( t # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID typ);
      cancel (&( t # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y);
      cancel (&( t # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z);
      cancel (store_string y v);
      cancel (store_term z b)
    | split_pures; dump_pre_spatial; try assumption ].
Qed.
