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
From SimpleC.EE.QCP_demos_human Require Import sll_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import sll_merge_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists s1. Exists s2. Exists (@nil Z).
  repeat (split_pure_spatial || split_pures).
  + cancel (sll x_pre s1).
    cancel (sll y_pre s2).
    cancel (((&( "ret" ))) # Ptr |->_).
    simpl.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial. reflexivity.
  + dump_pre_spatial.
    unfold merge_rel, merge_from_mid_rel.
    exact PreH1.
Qed.

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l1_new (y_data :: l2_new) (l3_2 ++ (x_data :: nil))%list.
  simpl sll. Exists y_next.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 t); [ | tauto].
    sep_apply (sllbseg_sllbseg (&( "ret" ))).
    cancel.
    sep_apply store_ptr_undef_store_ptr.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      subst.
      clear - PreH6 PreH1.
      unfold merge_from_mid_rel in *.
      rewrite (repeat_break_unfold _ _) in PreH6.
      prove_by_one_abs_step (by_continue (l1_new, y_data :: l2_new, l3_2 ++ x_data :: nil)).
      unfold merge_body.
      abs_choice_left.
      abs_test_step; [ lia | ].
      abs_ret_step.
    + dump_pre_spatial. exact PreH4.
Qed.

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (x_data :: l1_new) l2_new (l3_2 ++ (y_data :: nil))%list.
  simpl sll. Exists x_next.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 t); [ | tauto].
    sep_apply (sllbseg_sllbseg (&( "ret" ))).
    cancel.
    sep_apply store_ptr_undef_store_ptr.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      subst.
      clear - PreH6 PreH1.
      unfold merge_from_mid_rel in *.
      rewrite (repeat_break_unfold _ _) in PreH6.
      prove_by_one_abs_step (by_continue (x_data :: l1_new, l2_new, l3_2 ++ y_data :: nil)).
      unfold merge_body.
      abs_choice_right.
      abs_test_step; [ lia | ].
      abs_ret_step.
    + dump_pre_spatial. exact PreH5.
Qed.

Lemma proof_of_merge_return_wit_1 : merge_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero x); [ | exact PreH1].
  sep_apply sllseg_sll.
  Exists (l3 ++ l2).
  split_pure_spatial.
  - Intros_p Hl1.
    cancel.
  - Intros_p Hl1.
    dump_pre_spatial.
    subst l1.
    subst.
    clear - PreH2.
    unfold merge_from_mid_rel in PreH2.
    rewrite (repeat_break_unfold _ _) in PreH2.
    prove_by_one_abs_step (by_break (l3 ++ l2)).
    unfold merge_body.
    destruct l2; abs_ret_step.
Qed.

Lemma proof_of_merge_return_wit_2 : merge_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero y); [ | exact PreH1].
  sep_apply sllseg_sll.
  Exists (l3 ++ l1).
  split_pure_spatial.
  - Intros_p Hl2.
    cancel.
  - Intros_p Hl2.
    dump_pre_spatial.
    subst l2.
    subst; clear - PreH3.
    unfold merge_from_mid_rel in PreH3.
    rewrite (repeat_break_unfold _ _) in PreH3.
    prove_by_one_abs_step (by_break (l3 ++ l1)).
    unfold merge_body.
    destruct l1; abs_ret_step.
Qed.

Lemma proof_of_merge_which_implies_wit_3 : merge_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply sllbseg_2_sllseg.
  Intros ret'.
  Exists ret'.
  cancel.
Qed.

Lemma proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst x_pre.
  sep_apply_l_atomic (sll_zero 0 l_low_level_spec).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hlnil.
    subst l_low_level_spec.
    Exists q_pre_v_2. Exists p_pre_v_2. Exists l1_low_level_spec. Exists l2_low_level_spec.
    repeat (split_pure_spatial || split_pures).
    + cancel ((p_pre) # Ptr |-> p_pre_v_2).
      cancel (sll p_pre_v_2 l1_low_level_spec).
      cancel ((q_pre) # Ptr |-> q_pre_v_2).
      cancel (sll q_pre_v_2 l2_low_level_spec).
    + dump_pre_spatial.
      unfold split_rec_rel in PreH2.
      rewrite (split_rec_rel_unfold (nil, l1_low_level_spec, l2_low_level_spec)) in PreH2.
      simpl in PreH2.
      exact PreH2.
Qed.

Lemma proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p_callee_v. Exists q_callee_v. Exists s2_2. Exists s1_2.
  repeat (split_pure_spatial || split_pures).
  + cancel ((q_pre) # Ptr |-> p_callee_v).
    cancel (sll p_callee_v s1_2).
    cancel ((p_pre) # Ptr |-> q_callee_v).
    cancel (sll q_callee_v s2_2).
  + dump_pre_spatial.
    unfold reversepair, applyf.
    exact PreH1.
Qed.

Lemma proof_of_split_rec_which_implies_wit_2_split_goal_1 :
  split_rec_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst l_low_level_spec.
  unfold split_rec_rel in PreH1.
  rewrite (split_rec_rel_unfold (x_data :: l_new, l1_low_level_spec, l2_low_level_spec)) in PreH1.
  simpl in PreH1.
  tauto.
Qed.

Lemma proof_of_split_rec_which_implies_wit_2 : split_rec_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_split_rec_which_implies_wit_2_split_goal_1.
Qed.

Lemma proof_of_merge_sort_entail_wit_1_split_goal_1 :
  merge_sort_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mergesortrec_loc0.
  rewrite (mergesortrec_unfold l_low_level_spec) in PreH1.
  unfold mergesortrec_f in PreH1.
  tauto.
Qed.

Lemma proof_of_merge_sort_entail_wit_1 : merge_sort_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_merge_sort_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_merge_sort_entail_wit_2 : merge_sort_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (sll_not_zero q_callee_v s2).
  - dump_pre_spatial. exact PreH1.
  - Intros q_next. Intros h. Intros t.
    Exists s1. Exists (h :: t).
    repeat (split_pure_spatial || split_pures).
    + cancel (sll p_callee_v s1).
      simpl sll.
      Exists q_next.
      repeat (split_pure_spatial || split_pures).
      * cancel.
        cancel.
      * dump_pre_spatial.
        exact PreH1.
    + dump_pre_spatial.
      unfold applyf, maketuple, mergesortrec_loc0 in PreH2.
      rewrite H in PreH2.
      simpl in PreH2. exact PreH2.
    + dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l2_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0).
    cancel (sll q_callee_v l2_2).
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc1 in PreH1.
    exact PreH1.
  + dump_pre_spatial. exact PreH2.
Qed.

Lemma proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l1_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l1_2).
    cancel (sll retval_2 l0).
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc2 in PreH1.
    exact PreH1.
  + dump_pre_spatial. exact PreH2.
Qed.
(*
  sep_apply_l_atomic (sll_not_zero qv' s2).
  - dump_pre_spatial. exact PreH1.
  - Intros q_next. Intros h. Intros t.
    Exists s1. Exists (h :: t).
    repeat (split_pure_spatial || split_pures).
    + cancel (sll pv' s1).
      simpl.
      Exists q_next.
      repeat (split_pure_spatial || split_pures).
      * cancel (&(qv' # "list" ->ₛ"data") # Int |-> h).
        cancel (&(qv' # "list" ->ₛ"next") # Ptr |-> q_next).
        cancel (sll q_next t).
      * dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial.
      unfold applyf, maketuple, mergesortrec_loc0 in PreH2.
      rewrite H in PreH2.
      simpl in PreH2. exact PreH2.
*)

Lemma proof_of_merge_sort_return_wit_2 : merge_sort_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (sll_zero q_callee_v s2).
  * dump_pre_spatial. rewrite PreH1. reflexivity.
  * Intros_p Hs2nil.
    subst s2.
    Exists s1.
    repeat (split_pure_spatial || split_pures).
    + cancel (sll p_callee_v s1).
    + dump_pre_spatial.
      unfold applyf, maketuple, mergesortrec_loc0.
      simpl.
      exact PreH2.
Qed.

Lemma proof_of_merge_sort_partial_solve_wit_3_pure : merge_sort_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.


Lemma proof_of_merge_sort3_entail_wit_1_split_goal_1 :
  merge_sort3_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold gmergesortrec_loc0.
  rewrite (gmergesortrec_unfold l_low_level_spec) in PreH4.
  unfold gmergesortrec_f in PreH4.
  apply safeExec_choice_r in PreH4.
  unfold seq in PreH4.
  rewrite (split_rel_refine_ext_split l_low_level_spec).
  prove_by_one_abs_step tt.
  abs_test_step.
  lia.
Qed.

Lemma proof_of_merge_sort3_entail_wit_1 : merge_sort3_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_merge_sort3_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_merge_sort3_entail_wit_2 : merge_sort3_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists s1 s2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l2_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval_2 l0).
    cancel (sll q_callee_v l2_2).
  + dump_pre_spatial.
    unfold applyf, gmergesortrec_loc1 in PreH1.
    exact PreH1.
  + dump_pre_spatial. exact PreH2.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
Qed.

Lemma proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l1_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval_2 l1_2).
    cancel (sll retval_3 l0).
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc2 in PreH1.
    exact PreH1.
  + dump_pre_spatial. exact PreH2.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
Qed.

Lemma proof_of_merge_sort3_return_wit_2 : merge_sort3_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l0_2.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0_2).
  + dump_pre_spatial.
    rewrite (gmergesortrec_unfold l_low_level_spec) in PreH6.
    unfold gmergesortrec_f in PreH6.
    apply safeExec_choice_l in PreH6.
    eapply (safeExec_prorefine (ext_sort l_low_level_spec) (return l0_2)).
    - unfold StateRelMonad.ret, ext_sort.
      sets_unfold.
      intros s a s' [Ha Hs].
      subst.
      split; assumption.
    - exact PreH6.
Qed.

Lemma proof_of_merge_sort3_partial_solve_wit_5_pure : merge_sort3_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed. 

Lemma proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply safeExec_bind in H0 as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux.
  Exists X_low_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply (Hsafe_cont ATrue l0_2).
      exact H0.
  + repeat (split_pure_spatial || split_pures).
    - dump_pre_spatial. exact H.
    - dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_merge_sort3_derive_high_level_spec_by_low_level_spec : merge_sort3_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_high_level_spec.
  Exists (fun l0 _ => Permutation l_high_level_spec l0 /\ incr l0).
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply safeExec_ret in H0 as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj1 Hret).
    - dump_pre_spatial.
      apply safeExec_ret in H0 as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj2 Hret).
  + repeat (split_pure_spatial || split_pures).
    - dump_pre_spatial. exact H.
    - dump_pre_spatial.
      eapply safeExec_X_subset.
      * apply Hoare_result_state.
        apply functional_correctness_gmergesort.
      * apply safeExec_result_state.
        exists tt. exact I.
Qed.

Lemma proof_of_merge_sort2_derive_low_level_spec_aux_by_low_level_spec : merge_sort2_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux.
  Exists X_low_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply (Hsafe_cont ATrue l0_2).
      exact H.
  + dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_merge_sort2_derive_high_level_spec_by_low_level_spec : merge_sort2_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_high_level_spec.
  Exists (fun l0 _ => Permutation l_high_level_spec l0 /\ incr l0).
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj1 Hret).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj2 Hret).
  + dump_pre_spatial.
    eapply safeExec_X_subset.
    - apply Hoare_result_state.
      apply functional_correctness_gmergesort.
    - apply safeExec_result_state.
      exists tt. exact I.
Qed.

Lemma proof_of_merge_sort_derive_low_level_spec_aux_by_low_level_spec : merge_sort_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux.
  Exists X_low_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply (Hsafe_cont ATrue l0_2).
      exact H.
  + dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_high_level_spec.
  Exists (fun l0 _ => Permutation l_high_level_spec l0 /\ incr l0).
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj1 Hret).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj2 Hret).
  + dump_pre_spatial.
    eapply safeExec_X_subset.
    - apply Hoare_result_state.
      apply functional_correctness_mergesort.
    - apply safeExec_result_state.
      exists tt. exact I.
Qed.

Lemma proof_of_split_rec_derive_low_level_spec_aux_by_low_level_spec : split_rec_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros q_pre_v_aux.
  Intros p_pre_v_aux.
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux. Exists l1_low_level_spec_aux. Exists l2_low_level_spec_aux.
  Exists X_low_level_spec.
  Exists q_pre_v_aux. Exists p_pre_v_aux.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    cancel ((p_pre) # Ptr |-> p_pre_v_aux).
    cancel (sll p_pre_v_aux l1_low_level_spec_aux).
    cancel ((q_pre) # Ptr |-> q_pre_v_aux).
    cancel (sll q_pre_v_aux l2_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros qv'_2. Intros pv'_2. Intros s1_2. Intros s2_2.
    Exists qv'_2. Exists pv'_2. Exists s1_2. Exists s2_2.
    repeat (split_pure_spatial || split_pures).
    - cancel ((p_pre) # Ptr |-> pv'_2).
      cancel (sll pv'_2 s1_2).
      cancel ((q_pre) # Ptr |-> qv'_2).
      cancel (sll qv'_2 s2_2).
    - dump_pre_spatial.
      unfold applyf, maketuple.
      apply (Hsafe_cont ATrue (s1_2, s2_2)).
      exact H.
  + dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_split_rec_derive_high_level_spec_by_low_level_spec : split_rec_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros q_pre_v_high.
  Intros p_pre_v_high.
  Exists l_high_level_spec. Exists (@nil Z). Exists (@nil Z).
  Exists X_high_level_spec.
  Exists q_pre_v_high. Exists p_pre_v_high.
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    cancel ((p_pre) # Ptr |-> p_pre_v_high).
    cancel (sll p_pre_v_high (@nil Z)).
    cancel ((q_pre) # Ptr |-> q_pre_v_high).
    cancel (sll q_pre_v_high (@nil Z)).
    apply derivable1_wand_sepcon_adjoint.
    Intros qv'_2. Intros pv'_2. Intros s1_2. Intros s2_2.
    Exists qv'_2. Exists pv'_2. Exists s1_2. Exists s2_2.
    repeat (split_pure_spatial || split_pures).
    - cancel ((p_pre) # Ptr |-> pv'_2).
      cancel (sll pv'_2 s1_2).
      cancel ((q_pre) # Ptr |-> qv'_2).
      cancel (sll qv'_2 s2_2).
    - dump_pre_spatial. exact H0.
  + dump_pre_spatial.
    unfold split_rel in H.
    unfold split_rec_rel.
    exact H.
Qed. 
