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
From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof.
  pre_process.
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

Lemma proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Proof.
  pre_process.
  Exists l1_new. Exists (ydata :: l2_new). Exists (l3_2 ++ (xdata :: nil))%list.
  simpl sll. Exists ynext.
  repeat (split_pure_spatial || split_pures).
  + cancel (&((y) # "list" ->ₛ"data") # Int |-> ydata).
    cancel (&((y) # "list" ->ₛ"next") # Ptr |-> ynext).
    cancel (sll ynext l2_new).
    cancel (sll xnext l1_new).
    sep_apply_l_atomic (sllbseg_len1 t x xdata).
    * dump_pre_spatial. exact PreH3.
    * sep_apply_l_atomic (store_ptr_undef_store_ptr (&((x) # "list" ->ₛ"next")) xnext).
      cancel (&((x) # "list" ->ₛ"next") # Ptr |->_).
      sep_apply_l_atomic (sllbseg_sllbseg (&( "ret")) t (&((x) # "list" ->ₛ"next")) l3_2 (xdata :: nil)).
      cancel (sllbseg (&( "ret")) (&((x) # "list" ->ₛ"next")) (l3_2 ++ (xdata :: nil))%list).
  + dump_pre_spatial.
    rewrite PreH5 in PreH2.
    rewrite PreH6 in PreH2.
    unfold merge_from_mid_rel in PreH2 at 1.
    prog_nf in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    unfold merge_body in PreH2 at 1.
    prog_nf in PreH2.
    safe_choice_l PreH2; try lia.
    exact PreH2.
  + dump_pre_spatial. exact PreH4.
Qed.

Lemma proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Proof.
  pre_process.
  Exists (xdata :: l1_new). Exists l2_new. Exists (l3_2 ++ (ydata :: nil))%list.
  simpl sll. Exists xnext.
  repeat (split_pure_spatial || split_pures).
  + cancel (&((x) # "list" ->ₛ"data") # Int |-> xdata).
    cancel (&((x) # "list" ->ₛ"next") # Ptr |-> xnext).
    cancel (sll xnext l1_new).
    cancel (sll ynext l2_new).
    sep_apply_l_atomic (sllbseg_len1 t y ydata).
    * dump_pre_spatial. exact PreH4.
    * sep_apply_l_atomic (store_ptr_undef_store_ptr (&((y) # "list" ->ₛ"next")) ynext).
      cancel (&((y) # "list" ->ₛ"next") # Ptr |->_).
      sep_apply_l_atomic (sllbseg_sllbseg (&( "ret")) t (&((y) # "list" ->ₛ"next")) l3_2 (ydata :: nil)).
      cancel (sllbseg (&( "ret")) (&((y) # "list" ->ₛ"next")) (l3_2 ++ (ydata :: nil))%list).
  + dump_pre_spatial.
    rewrite PreH5 in PreH2.
    rewrite PreH6 in PreH2.
    unfold merge_from_mid_rel in PreH2 at 1.
    prog_nf in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    unfold merge_body in PreH2 at 1.
    prog_nf in PreH2.
    safe_choice_r PreH2; try lia.
    exact PreH2.
  + dump_pre_spatial. exact PreH3.
Qed.

Lemma proof_of_merge_entail_wit_4_1 : merge_entail_wit_4_1.
Proof.
  pre_process.
  subst x.
  sep_apply_l_atomic (sll_zero 0 l1).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hl1nil.
    subst l1.
    sep_apply_l_atomic (sllbseg_2_sllseg (&( "ret")) t y l3).
    Intros ret.
    Exists ret. Exists (l3 ++ l2).
    repeat (split_pure_spatial || split_pures).
    + cancel (&( "ret") # Ptr |-> ret).
      sep_apply_l_atomic (sllseg_sll ret y l3 l2).
      cancel (sll ret (l3 ++ l2)).
    + dump_pre_spatial.
      unfold merge_from_mid_rel in PreH2 at 1.
      prog_nf in PreH2.
      unfold_loop in PreH2.
      prog_nf in PreH2.
      unfold merge_body in PreH2 at 1.
      prog_nf in PreH2.
      exact PreH2.
Qed.

Lemma proof_of_merge_entail_wit_4_2 : merge_entail_wit_4_2.
Proof.
  pre_process.
  subst y.
  sep_apply_l_atomic (sll_zero 0 l2).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hl2nil.
    subst l2.
    sep_apply_l_atomic (sllbseg_2_sllseg (&( "ret")) t x l3).
    Intros ret.
    Exists ret. Exists (l3 ++ l1).
    repeat (split_pure_spatial || split_pures).
    + cancel (&( "ret") # Ptr |-> ret).
      sep_apply_l_atomic (sllseg_sll ret x l3 l1).
      cancel (sll ret (l3 ++ l1)).
    + dump_pre_spatial.
      unfold merge_from_mid_rel in PreH3 at 1.
      prog_nf in PreH3.
      unfold_loop in PreH3.
      prog_nf in PreH3.
      unfold merge_body in PreH3 at 1.
      destruct l1 as [|h tl]; prog_nf in PreH3; exact PreH3.
Qed.

Lemma proof_of_merge_return_wit_1_manual : merge_return_wit_1.
Proof.
  pre_process.
  Exists s3_2.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll ret s3_2).
  + dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Proof.
  pre_process.
  Exists pv'_2. Exists qv'_2. Exists s2_2. Exists s1_2.
  repeat (split_pure_spatial || split_pures).
  + cancel ((q_pre) # Ptr |-> pv'_2).
    cancel (sll pv'_2 s1_2).
    cancel ((p_pre) # Ptr |-> qv'_2).
    cancel (sll qv'_2 s2_2).
  + dump_pre_spatial.
    unfold reversepair, applyf.
    exact PreH1.
Qed.

Lemma proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Proof.
  pre_process.
  subst x_pre.
  sep_apply_l_atomic (sll_zero 0 l_low_level_spec).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hlnil.
    subst l_low_level_spec.
    Exists qv_low_level_spec. Exists pv_low_level_spec. Exists l1_low_level_spec. Exists l2_low_level_spec.
    repeat (split_pure_spatial || split_pures).
    + cancel ((p_pre) # Ptr |-> pv_low_level_spec).
      cancel (sll pv_low_level_spec l1_low_level_spec).
      cancel ((q_pre) # Ptr |-> qv_low_level_spec).
      cancel (sll qv_low_level_spec l2_low_level_spec).
    + dump_pre_spatial.
      unfold split_rec_rel in PreH2.
      rewrite (split_rec_rel_unfold (nil, l1_low_level_spec, l2_low_level_spec)) in PreH2.
      simpl in PreH2.
      exact PreH2.
Qed.

Lemma proof_of_split_rec_entail_wit_2 : split_rec_entail_wit_2.
Proof.
  pre_process.
  Exists l_new_2. Exists x_data_2.
  repeat (split_pure_spatial || split_pures).
  + cancel ((q_pre) # Ptr |-> qv_low_level_spec).
    cancel (sll qv_low_level_spec l2_low_level_spec).
    cancel (sll x_next l_new_2).
    simpl sll.
    Exists pv_low_level_spec.
    split_pure_spatial.
    - cancel (&((x_pre) # "list" ->ₛ"data") # Int |-> x_data_2).
      cancel (&((x_pre) # "list" ->ₛ"next") # Ptr |-> pv_low_level_spec).
      cancel (sll pv_low_level_spec l1_low_level_spec).
      entailer!.
    - dump_pre_spatial. exact PreH1.
  + dump_pre_spatial. exact PreH1.
  + dump_pre_spatial.
    rewrite PreH3 in PreH2.
    unfold split_rec_rel in PreH2.
    rewrite (split_rec_rel_unfold (x_data_2 :: l_new_2, l1_low_level_spec, l2_low_level_spec)) in PreH2.
    simpl in PreH2.
    exact PreH2.
  + dump_pre_spatial. exact PreH3.
Qed.

Lemma proof_of_split_rec_partial_solve_wit_1_pure_manual : split_rec_partial_solve_wit_1_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort_partial_solve_wit_1_pure : merge_sort_partial_solve_wit_1_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Proof.
  pre_process.
  subst p. subst q.
  simpl sll.
  repeat (split_pure_spatial || split_pures).
  + Intros_p Hp0. Intros_p Hq0. cancel.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial.
    unfold mergesortrec in PreH3 at 1.
    erewrite (program_para_equiv (mergesortrec_unfold)) in PreH3.
    unfold mergesortrec_f, mergesortrec_loc0 in PreH3.
    exact PreH3.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
Proof.
  pre_process.
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
Qed.

Lemma proof_of_merge_sort_entail_wit_5 : merge_sort_entail_wit_5.
Proof.
  pre_process.
  Exists l2_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0).
    cancel (sll q l2_2).
  + dump_pre_spatial. exact PreH2.
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc1 in PreH1.
    unfold mergesortrec_loc2.
    exact PreH1.
Qed.

Lemma proof_of_merge_sort_entail_wit_6 : merge_sort_entail_wit_6.
Proof.
  pre_process.
  Exists l1_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0).
    cancel (sll p l1_2).
  + dump_pre_spatial.
    unfold applyf in PreH1 at 1.
    unfold mergesortrec_loc2 in PreH1 at 1.
    prog_nf in PreH1.
    exact PreH1.
Qed.

Lemma proof_of_merge_sort_return_wit_2 : merge_sort_return_wit_2.
Proof.
  pre_process.
  sep_apply_l_atomic (sll_zero qv' s2).
  * dump_pre_spatial. rewrite PreH1. reflexivity.
  * Intros_p Hs2nil.
    subst s2.
    Exists s1.
    repeat (split_pure_spatial || split_pures).
    + cancel (sll pv' s1).
    + dump_pre_spatial.
      unfold applyf, maketuple, mergesortrec_loc0.
      simpl.
      exact PreH2.
Qed.

Lemma proof_of_merge_sort_partial_solve_wit_3_pure_manual : merge_sort_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Proof.
  pre_process.
  subst p. subst q.
  simpl sll.
  repeat (split_pure_spatial || split_pures).
  + Intros_p Hp0. Intros_p Hq0. cancel.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
  + dump_pre_spatial.
    rewrite (gmergesortrec_unfold l_low_level_spec) in PreH5.
    unfold gmergesortrec_f in PreH5.
    apply safeExec_choice_r in PreH5.
    apply safeExec_test_bind in PreH5; [|lia].
    refine (safeExec_prorefine
        (x <- ext_split l_low_level_spec ;; gmergesortrec_loc0 x)
        (x <- split_rel l_low_level_spec ;; gmergesortrec_loc0 x)
        ATrue X_low_level_spec _ PreH5).
    apply programbind_included_Proper.
    - apply split_rel_refine_ext_split.
    - reflexivity.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
Proof.
  pre_process.
  Exists s1. Exists s2.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll pv' s1).
    cancel (sll qv' s2).
  + dump_pre_spatial.
    unfold applyf in PreH1 at 1.
    unfold maketuple in PreH1 at 1.
    unfold gmergesortrec_loc0 in PreH1 at 1.
    prog_nf in PreH1.
    exact PreH1.
Qed.

Lemma proof_of_merge_sort3_entail_wit_5 : merge_sort3_entail_wit_5.
Proof.
  pre_process.
  Exists l2_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0).
    cancel (sll q l2_2).
  + dump_pre_spatial.
    unfold applyf, gmergesortrec_loc1.
    exact PreH1.
Qed.

Lemma proof_of_merge_sort3_entail_wit_6 : merge_sort3_entail_wit_6.
Proof.
  pre_process.
  Exists l1_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0).
    cancel (sll p l1_2).
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc2.
    exact PreH1.
Qed.

Lemma proof_of_merge_sort3_partial_solve_wit_3_pure : merge_sort3_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort3_return_wit_2 : merge_sort3_return_wit_2.
Proof.
  pre_process.
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

Lemma proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
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
  pre_process.
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
  pre_process.
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
  pre_process.
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
  pre_process.
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
  pre_process.
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
  pre_process.
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux. Exists l1_low_level_spec_aux. Exists l2_low_level_spec_aux.
  Exists X_low_level_spec.
  Exists pv_low_level_spec_aux. Exists qv_low_level_spec_aux.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    cancel ((p_pre) # Ptr |-> pv_low_level_spec_aux).
    cancel (sll pv_low_level_spec_aux l1_low_level_spec_aux).
    cancel ((q_pre) # Ptr |-> qv_low_level_spec_aux).
    cancel (sll qv_low_level_spec_aux l2_low_level_spec_aux).
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
  pre_process.
  Exists l_high_level_spec. Exists (@nil Z). Exists (@nil Z).
  Exists X_high_level_spec.
  Exists pv_high_level_spec. Exists qv_high_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    cancel ((p_pre) # Ptr |-> pv_high_level_spec).
    cancel (sll pv_high_level_spec (@nil Z)).
    cancel ((q_pre) # Ptr |-> qv_high_level_spec).
    cancel (sll qv_high_level_spec (@nil Z)).
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
