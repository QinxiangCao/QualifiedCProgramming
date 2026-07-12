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
  pre_process.
  prop_apply CharArray.full_Zlength.
  prop_apply IntArray.full_Zlength.
  rewrite Zlength_app.
  replace (Zlength (0::nil)) with 1 by easy.
  pose proof PreH1 as H'.
  unfold inner_loop in PreH1.
  unfold_loop in PreH1.
  unfold inner_body at 1 in PreH1.
  safe_step PreH1.
  entailer!.
Qed. 

Lemma proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Proof. 
  pre_process.
  entailer!.
  unfold inner_loop in *.
  unfold_loop in PreH5.
  unfold inner_body at 1 in PreH5.
  safe_step PreH5.
  rewrite app_Znth1 in PreH2 by auto.
  safe_choice_r PreH5.
  safe_choice_r PreH5; auto.
  unfold continue in PreH5.
  prog_nf in PreH5. auto.
Qed. 

Lemma proof_of_inner_return_wit_2 : inner_return_wit_2.
Proof. 
  pre_process.
  entailer!.
  unfold inner_loop in PreH4.
  unfold_loop in PreH4.
  unfold inner_body at 1 in PreH4.
  repeat (prog_nf in PreH4 ; safe_step PreH4).
  rewrite app_Znth1 in PreH1 by lia.
  safe_choice_l PreH4; auto.
  unfold break in PreH4.
  prog_nf in PreH4. auto.
Qed. 

Lemma proof_of_inner_return_wit_1 : inner_return_wit_1.
Proof. 
  pre_process.
  entailer!.
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
Qed. 

Lemma proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Proof. 
  pre_process; subst.
  Exists (sublist 1 n_low_level_spec l) (0::nil).
  entailer!.
  prop_apply IntArray.full_Zlength; Intros.
  destruct l.
  rewrite Zlength_nil in H; lia.
  replace (z::l) with ((z::nil) ++ l) by easy.
  rewrite (replace_Znth_app_l 0 0); try lia.
  2:{ lazy; auto. }
  replace (replace_Znth 0 0 (z::nil)) with (0::nil) by easy.
  rewrite (IntArray.full_split_to_full retval 1 n_low_level_spec); try lia.
  rewrite sublist_split_app_l; [ | lia | easy].
  assert (Zlength (0::nil) = 1). 
  { lazy; auto. }
  rewrite sublist_self; eauto.
  entailer!.
  replace ((0::nil) ++ l) with (0::l) by easy.
  replace ((z::nil) ++ l) with (z::l) by easy.
  rewrite replace_Znth_length in H.
  rewrite (sublist_cons2 1 n_low_level_spec); try lia.
  2:{
    rewrite Zlength_cons.
    rewrite Zlength_cons in H. lia. 
  }
  rewrite (sublist_cons2 1 n_low_level_spec); try lia.
  entailer!.
Qed. 

Lemma proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Proof. 
  pre_process.
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
  entailer!.
Qed. 

Lemma proof_of_constr_return_wit_1 : constr_return_wit_1.
Proof. 
  pre_process.
  prop_apply (IntArray.full_length (vnext_2 + i * sizeof ( INT ))); Intros.
  assert (i = n_low_level_spec) by lia; subst i; clear H.
  prop_apply CharArray.full_Zlength.  
  Exists vnext0; entailer!.
  - replace (n_low_level_spec-n_low_level_spec) with 0 by lia.
    prop_apply (IntArray.full_Zlength (vnext_2 + n_low_level_spec * sizeof ( INT ))).
    Intros; apply Zlength_nil_inv in H0; subst l0.
    cbn. entailer!.
  - unfold constr_loop_from in PreH2.
    unfold_loop in PreH2.
    apply string_Zlength in H.
    safe_choice_r PreH2.
    auto. lia.
Qed. 

Lemma proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Proof. 
  pre_process.
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
  pre_process.
  prop_apply IntArray.full_length; Intros.
  destruct l0.
  simpl in H; lia.
  Exists z l0; entailer!.
  rewrite <- Zlength_correct in H.
  rewrite (IntArray.full_unfold).
  replace (vnext + i * sizeof ( INT ) + 0 * sizeof ( INT )) with (vnext + i * sizeof ( INT )) by lia.
  sep_apply IntArray.seg_to_full.
  replace (vnext + i * sizeof ( INT ) + 1 * sizeof ( INT )) with (vnext + (i+1) * sizeof ( INT )) by lia.
  replace (n_low_level_spec - i - 1) with (n_low_level_spec - (i + 1)) by lia.
  entailer!.
Qed. 

Lemma proof_of_match_entail_wit_1 : match_entail_wit_1.
Proof.
  pre_process.
  subst; entailer!.
Qed. 

Lemma proof_of_match_entail_wit_2 : match_entail_wit_2.
Proof. 
  pre_process.
  prop_apply CharArray.full_Zlength; entailer!.
  apply string_Zlength in H. 
  unfold match_loop_from_after, applyf in PreH2.
  safe_choice_r PreH2; [unfold continue in PreH2; prog_nf in PreH2; auto | lia].
Qed. 

Lemma proof_of_match_return_wit_2 : match_return_wit_2.
Proof.
  pre_process; subst.
  unfold match_loop_from_after, applyf in PreH2.
  prop_apply CharArray.full_Zlength; Intros.
  apply string_Zlength in H.
  rewrite H in *; clear H.
  Exists (Some(i-n_low_level_spec+1)); entailer!.
  safe_choice_l PreH2; try lia.
  unfold break in PreH2.
  prog_nf in PreH2.
  exact PreH2.
Qed. 

Lemma proof_of_match_return_wit_1 : match_return_wit_1.
Proof. 
  pre_process.
  prop_apply (CharArray.full_Zlength text_pre).
  Exists None; entailer!.
  apply string_Zlength in H.
  unfold match_loop_from in PreH2.
  unfold_loop in PreH2.
  prog_nf in PreH2.
  safe_choice_r PreH2; [unfold continue in PreH2 ; prog_nf in PreH2 ; auto | lia].
Qed. 

Lemma proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Proof. 
  pre_process.
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
  pre_process.
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
	  do 2 apply derivable1_wand_sepcon_adjoint.
	  entailer!.
	  2:{
	    subst prog.
	    apply safeExec_monad_Atrue_finnal.
	    intro Herr.
	    eapply (proj2 H7); [exact I | exact Herr].
	  }
	  apply derivable1_wand_sepcon_adjoint.
	  entailer!. Intros ret retval.
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
	  - Right; Exists z.
	    subst retval; entailer!.
	    apply first_occur_nonneg in Hpost; auto.
	  - Left; Exists (-1); entailer!.
Qed.

Lemma proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Proof. 
  pre_process.
  prop_apply CharArray.full_Zlength; Intros.
  apply string_Zlength in H1.
  Exists str_high_level_spec n_high_level_spec.
	  assert (Zlength str_high_level_spec > 0) by lia.
	  apply Zlength_nonnil in H2.
	  pose proof constr_loop_sound 0 str_high_level_spec H2.
	  Exists (fun r x => (constr_loop 0 str_high_level_spec).(MonadErr.nrm) tt r x).
	  entailer!.
	  2:{
	    apply safeExec_monad_Atrue_finnal.
	    intro Herr.
	    eapply (proj2 H3); [exact I | exact Herr].
	  }
	  apply derivable1_wand_sepcon_adjoint.
	  entailer!; Intros vnext retval.
	  Exists vnext retval; entailer!.
	  destruct (@Hoare_safeexec_compose unit (list Z)
	              ATrue
	              (constr_loop 0 str_high_level_spec)
	              (fun vnext _ =>
	                 is_prefix_func vnext str_high_level_spec /\
	                 Zlength vnext = Zlength str_high_level_spec)
	              H3 ATrue vnext tt H4 I) as [σ [[Hprefix _] _]].
	  exact Hprefix.
Qed. 

Lemma proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.
Proof.
  pre_process.
  prop_apply CharArray.full_Zlength; Intros.
  prop_apply IntArray.full_Zlength; Intros.
  apply string_Zlength in H2.
  apply safeExec_bind in H as (X' & H7 & H8).
  Exists str0_bind_spec vnext0_bind_spec.
  Exists n_bind_spec m_bind_spec X'; entailer!.
  apply derivable1_wand_sepcon_adjoint; entailer!.
  Intros ret; Exists ret; entailer!.
Qed. 
