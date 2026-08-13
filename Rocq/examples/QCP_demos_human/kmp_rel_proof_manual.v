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
From SimpleC.EE.QCP_demos_human Require Import kmp_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.


From SimpleC.EE.QCP_demos_human Require Import kmp_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply CharArray.full_Zlength.
  prop_apply IntArray.full_Zlength.
  rewrite Zlength_app.
  replace (Zlength (0::nil)) with 1 by easy.
  pose proof PreH1 as H'.
  unfold inner_loop in PreH1.
  unfold_loop in PreH1.
  unfold inner_body at 1 in PreH1.
  safe_step PreH1.
  split_pure_spatial.
  - Intros_p Hlen_str.
    Intros_p Hlen_vnext.
    cancel.
  - split_pures.
    + Intros H6.
      Intros H7.
      dump_pre_spatial.
      lia.
    + Intros H6.
      Intros H7.
      dump_pre_spatial.
      lia.
    + Intros H6.
      Intros H7.
      dump_pre_spatial.
      exact H'.
    + Intros H6.
      Intros H7.
      dump_pre_spatial.
      lia.
    + Intros H6.
      Intros H7.
      dump_pre_spatial.
      lia.
Qed. 

Lemma proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Proof. 
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold inner_loop in *.
      unfold_loop in PreH5.
      unfold inner_body in PreH5.
      safe_step PreH5.
      rewrite app_Znth1 in PreH2 by auto.
      safe_choice_r PreH5.
      safe_choice_r PreH5; auto.
      unfold continue in PreH5.
      prog_nf in PreH5. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_inner_return_wit_2 : inner_return_wit_2.
Proof. 
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold inner_loop in PreH4.
      unfold_loop in PreH4.
      unfold inner_body in PreH4.
      repeat (prog_nf in PreH4 ; safe_step PreH4).
      rewrite app_Znth1 in PreH1 by lia.
      safe_choice_l PreH4; auto.
      unfold break in PreH4.
      prog_nf in PreH4. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_inner_return_wit_1 : inner_return_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold inner_loop in PreH5.
      unfold_loop in PreH5.
      unfold inner_body at 1 in PreH5.
      safe_step PreH5.
      rewrite app_Znth1 in PreH2 by lia.
      safe_choice_r PreH5.
      safe_choice_l PreH5.
      unfold break in PreH5.
      prog_nf in PreH5.
      auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto); subst.
  subst retval_2.
  Exists (sublist 1 n_low_level_spec l) (0::nil).
  split_pure_spatial.
  - prop_apply IntArray.full_Zlength; Intros_p Hlen.
    destruct l.
    + rewrite replace_Znth_length in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    + replace (z::l) with ((z::nil) ++ l) by easy.
      rewrite (replace_Znth_app_l 0 0); try lia.
      2:{ lazy; auto. }
      replace (replace_Znth 0 0 (z::nil)) with (0::nil) by easy.
      rewrite (IntArray.full_split_to_full retval 1 n_low_level_spec); try lia.
      rewrite sublist_split_app_l; [ | lia | easy].
      assert (Zlength (0::nil) = 1).
      { lazy; auto. }
      rewrite sublist_self; eauto.
      replace ((0::nil) ++ l) with (0::l) by easy.
      replace ((z::nil) ++ l) with (z::l) by easy.
      rewrite replace_Znth_length in Hlen.
      rewrite (sublist_cons2 1 n_low_level_spec); try lia.
      2:{
        rewrite Zlength_cons.
        rewrite Zlength_cons in Hlen. lia.
      }
      rewrite (sublist_cons2 1 n_low_level_spec); try lia.
      cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold constr_loop in PreH2.
      cbn in PreH2.
      unfold constr_loop_from.
      cbn.
      exact PreH2.
    + dump_pre_spatial.
      exact PreH4.
    + dump_pre_spatial.
      lia.
Qed. 

Lemma proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength vnext).
  Intros_p Hlen.
  assert (Hvnext0_len : Zlength vnext0_2 = i).
  {
    rewrite Zlength_replace_Znth in Hlen.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
    lia.
  }
  assert (Hrep :
    replace_Znth i retval (vnext0_2 ++ (a :: nil)) =
    vnext0_2 ++ (retval :: nil)).
  {
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i - Zlength vnext0_2) with 0 by lia.
    unfold replace_Znth. simpl. reflexivity.
  }
  Exists l1 (vnext0_2 ++ (retval :: nil)).
  rewrite Hrep.
  unfold constr_loop_from_after in PreH2.
  split_pure_spatial.
  - cancel (IntArray.full vnext (i + 1) (vnext0_2 ++ retval :: nil)).
    cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_constr_return_wit_1 : constr_return_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_length (vnext_2 + i * sizeof ( INT ))); Intros.
  assert (i = n_low_level_spec) by lia; subst i.
  prop_apply CharArray.full_Zlength.
  Intros_p Hstr.
  Exists vnext0.
  prop_apply (IntArray.full_Zlength (vnext_2 + n_low_level_spec * sizeof ( INT ))).
  Intros_p Hnil.
  split_pure_spatial.
  - replace (n_low_level_spec - n_low_level_spec) with 0 in Hnil by lia.
    apply Zlength_nil_inv in Hnil; subst l0.
    cbn.
    Intros_p Hzero.
    Intros_p Hnil_eq.
    cancel.
  - apply string_Zlength in Hstr.
    unfold constr_loop_from in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    safe_choice_r PreH2; try lia.
    dump_pre_spatial.
    exact PreH2.
Qed. 

Lemma proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Proof. 
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_length vnext).
  Intros_p Hvnext_len.
  prop_apply CharArray.full_Zlength.
  Intros_p Hstr.
  apply string_Zlength in Hstr.
  split_pures.
  - dump_pre_spatial.
    unfold constr_loop_from in PreH2.
    rewrite Hstr in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    safe_choice_l PreH2; try lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    unfold constr_loop_from in PreH2.
    rewrite Hstr in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    safe_choice_l PreH2; try lia.
    unfold constr_body at 1 in PreH2.
    prog_nf in PreH2.
    safe_step PreH2.
    prog_nf in PreH2.
    unfold constr_loop_from_after.
    rewrite app_Znth1 by lia.
    unfold constr_loop_from.
    rewrite Hstr.
    exact PreH2.
Qed.

Lemma proof_of_constr_which_implies_wit_1 : constr_which_implies_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length; Intros_p H.
  destruct l0.
  simpl in H; lia.
  Exists z l0.
  split_pure_spatial.
  - rewrite <- Zlength_correct in H.
    rewrite (IntArray.full_unfold).
    replace (vnext + i * sizeof ( INT ) + 0 * sizeof ( INT )) with (vnext + i * sizeof ( INT )) by lia.
    sep_apply IntArray.seg_to_full.
    replace (vnext + i * sizeof ( INT ) + 1 * sizeof ( INT )) with (vnext + (i+1) * sizeof ( INT )) by lia.
    replace (n_low_level_spec - i - 1) with (n_low_level_spec - (i + 1)) by lia.
    cancel.
  - dump_pre_spatial.
    reflexivity.
Qed. 

Lemma proof_of_match_entail_wit_1 : match_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_match_entail_wit_2 : match_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply CharArray.full_Zlength.
  Intros_p Hpatn.
  apply string_Zlength in Hpatn.
  subst retval_2 retval.
  split_pure_spatial.
  - cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
  - split_pures.
    + dump_pre_spatial.
      unfold match_loop_from_after, applyf in PreH2.
      rewrite Hpatn in PreH2.
      safe_choice_r PreH2; [unfold continue in PreH2; prog_nf in PreH2; exact PreH2 | lia].
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_match_return_wit_2 : match_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto); subst.
  unfold match_loop_from_after, applyf in PreH2.
  prop_apply CharArray.full_Zlength; Intros_p H.
  apply string_Zlength in H.
  rewrite H in *; clear H.
  Exists (Some(i-n_low_level_spec+1)).
  split_pure_spatial.
  - cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
  - split_pures.
    + dump_pre_spatial.
      safe_choice_l PreH2; try lia.
      unfold break in PreH2.
      prog_nf in PreH2.
      exact PreH2.
    + dump_pre_spatial.
      reflexivity.
Qed. 

Lemma proof_of_match_return_wit_1 : match_return_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  prop_apply (CharArray.full_Zlength text_pre).
  Intros_p Htext.
  Exists None.
  split_pure_spatial.
  - cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
  - split_pures.
    + apply string_Zlength in Htext.
      dump_pre_spatial.
      unfold match_loop_from in PreH2.
      rewrite Htext in PreH2.
      unfold_loop in PreH2.
      prog_nf in PreH2.
      safe_choice_r PreH2; try lia.
      unfold continue in PreH2; prog_nf in PreH2; exact PreH2.
    + dump_pre_spatial.
      reflexivity.
Qed. 

Lemma proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Proof. 
  LLM_pre_process ltac:(int_auto).
  prop_apply CharArray.full_Zlength.
  Intros_p Htext.
  apply string_Zlength in Htext.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    unfold match_loop_from in PreH2.
    rewrite Htext in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    safe_choice_l PreH2; try lia.
    unfold match_body at 1 in PreH2.
    prog_nf in PreH2.
    safe_step PreH2.
    prog_nf in PreH2.
    unfold match_loop_from_after.
    rewrite app_Znth1 by lia.
    unfold match_loop_from.
    rewrite Htext.
    exact PreH2.
Qed. 

Lemma proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists patn0_high_level_spec text0_high_level_spec vnext0_high_level_spec n_high_level_spec.
  remember (match_loop 0 patn0_high_level_spec text0_high_level_spec vnext0_high_level_spec) as prog.
  Exists m_high_level_spec (fun (r: option Z) x => prog.(MonadErr.nrm) tt r x).
  do 2 prop_apply CharArray.full_Zlength; Intros.
  prop_apply IntArray.full_length; Intros.
  apply string_Zlength in H3.
  apply string_Zlength in H4.
  rewrite <- Zlength_correct in H5.
  assert (Zlength patn0_high_level_spec > 0) by lia.
  rewrite <- Zlength_nonnil in H6.
  pose proof match_loop_sound 0 patn0_high_level_spec text0_high_level_spec vnext0_high_level_spec H6 ltac:(lia) H.
	  split_pure_spatial.
	  - cancel.
	    apply derivable1_wand_sepcon_adjoint.
	    Intros ret retval.
	    subst prog.
	    destruct (@Hoare_safeexec_compose unit (option Z)
	                ATrue
	                (match_loop 0 patn0_high_level_spec text0_high_level_spec
	                   vnext0_high_level_spec)
	                (fun res _ =>
	                   match res with
	                   | Some r => first_occur patn0_high_level_spec text0_high_level_spec r
	                   | None => no_occurance patn0_high_level_spec text0_high_level_spec
	                   end)
	                H7 ATrue ret tt H8 I) as [σ [Hpost _]].
	    destruct ret; simpl in H9.
	    + Right; Exists z.
	      split_pure_spatial.
	      * cancel (CharArray.full patn_pre (n_high_level_spec + 1) (patn0_high_level_spec ++ 0 :: nil)).
	        cancel (CharArray.full text_pre (m_high_level_spec + 1) (text0_high_level_spec ++ 0 :: nil)).
	        cancel (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec).
	      * split_pures.
	        -- dump_pre_spatial. apply first_occur_nonneg in Hpost; auto.
	        -- dump_pre_spatial. exact Hpost.
    + Left; Exists (-1).
      split_pure_spatial.
      * cancel (CharArray.full patn_pre (n_high_level_spec + 1) (patn0_high_level_spec ++ 0 :: nil)).
        cancel (CharArray.full text_pre (m_high_level_spec + 1) (text0_high_level_spec ++ 0 :: nil)).
        cancel (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec).
	      * split_pures.
	        -- dump_pre_spatial. reflexivity.
	        -- dump_pre_spatial. exact Hpost.
	  - split_pures.
	    + dump_pre_spatial.
	      subst prog.
	      apply safeExec_monad_Atrue_finnal.
	      intro Herr.
	      eapply (proj2 H7); [exact I | exact Herr].
	    + dump_pre_spatial. lia.
	    + dump_pre_spatial. lia.
	    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply CharArray.full_Zlength; Intros.
  apply string_Zlength in H1.
  Exists str_high_level_spec n_high_level_spec.
  assert (Zlength str_high_level_spec > 0) by lia.
  apply Zlength_nonnil in H2.
  pose proof constr_loop_sound 0 str_high_level_spec H2.
  Exists (fun r x => (constr_loop 0 str_high_level_spec).(MonadErr.nrm) tt r x).
  split_pure_spatial.
  - cancel.
    apply derivable1_wand_sepcon_adjoint.
	    Intros vnext retval.
	    Exists vnext retval.
	    split_pure_spatial.
	    + cancel.
	    + dump_pre_spatial.
	      destruct (@Hoare_safeexec_compose unit (list Z)
	                  ATrue
	                  (constr_loop 0 str_high_level_spec)
	                  (fun vnext _ =>
	                     is_prefix_func vnext str_high_level_spec /\
	                     Zlength vnext = Zlength str_high_level_spec)
	                  H3 ATrue vnext tt H4 I) as [σ [[Hprefix _] _]].
	      exact Hprefix.
	  - split_pures.
	    + dump_pre_spatial.
	      apply safeExec_monad_Atrue_finnal.
	      intro Herr.
	      eapply (proj2 H3); [exact I | exact Herr].
	    + dump_pre_spatial. lia.
	    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply CharArray.full_Zlength; Intros.
  prop_apply IntArray.full_Zlength; Intros.
  apply string_Zlength in H2.
  apply safeExec_bind in H as (X' & H7 & H8).
  Exists str0_bind_spec vnext0_bind_spec n_bind_spec m_bind_spec X'.
  split_pure_spatial.
  - cancel (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec).
    cancel (CharArray.full str_pre (n_bind_spec + 1) (str0_bind_spec ++ 0 :: nil)).
    apply derivable1_wand_sepcon_adjoint.
    Intros ret.
    Exists ret.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial. apply H8. exact H.
      * dump_pre_spatial. exact H4.
      * dump_pre_spatial. exact H5.
  - split_pures.
    + dump_pre_spatial. exact H7.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
Qed.
