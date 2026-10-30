From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.alpha_equiv Require Import thm_apply_goal.
From SimpleC.EE.Applications_human.alpha_equiv Require Import thm_apply_lib.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.Applications_human.alpha_equiv.ast_lib.
Require Import SimpleC.EE.Applications_human.alpha_equiv.thm_apply_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_sub_thm_return_wit_1_split_goal_spatial : sub_thm_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_var_sub.
  destruct vs.
  Intros y z.
  pose proof (sll_var_sub_list_fold lis_pre lis_cur l0 y z name t0 lis_next) as Hfold.
  pose proof (Hfold ltac:(unfold NULL in *; lia) ltac:(unfold NULL in *; lia)) as Hfold_inst.
  sep_apply Hfold_inst.
  rewrite PreH5.
  unfold store_sub_thm_res.
  destruct t.
  + pose proof thm_subst_allres_var var (VarSub name t0) l0 as Hall.
    rewrite Hall.
    pose proof thm_subst'_var var (VarSub name t0) l0 as Hsubst.
    rewrite Hsubst.
    unfold store_term, store_term'.
    Intros x; Exists x.
    split_pure_spatial.
    - cancel (&( thm_pre # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> x).
      cancel (store_string x var).
      cancel (sll_var_sub_list lis_pre (VarSub name t0 :: l0)).
      cancel (&( thm_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermVar var)).
    - unfold NULL in *; split_pures; dump_pre_spatial; try reflexivity; try assumption.
  + pose proof thm_subst_allres_const ctype content (VarSub name t0) l0 as Hall.
    rewrite Hall.
    pose proof thm_subst'_const ctype content (VarSub name t0) l0 as Hsubst.
    rewrite Hsubst.
    unfold store_term, store_term'.
    split_pure_spatial.
    - cancel (&( thm_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermConst ctype content)).
      cancel (&( thm_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype).
      cancel (&( thm_pre # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content).
      cancel (sll_var_sub_list lis_pre (VarSub name t0 :: l0)).
    - unfold NULL in *; split_pures; dump_pre_spatial; try reflexivity; try assumption.
  + pose proof thm_subst_allres_apply t1 t2 (VarSub name t0) l0 as Hall.
    rewrite Hall.
    pose proof thm_subst'_apply t1 t2 (VarSub name t0) l0 as Hsubst.
    rewrite Hsubst.
    unfold store_term, store_term'.
    fold store_term.
    Intros x sy; Exists x sy.
    split_pure_spatial.
    - cancel (&( thm_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermApply t1 t2)).
      cancel (&( thm_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> x).
      cancel (&( thm_pre # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> sy).
      cancel (store_term x t1).
      cancel (store_term sy t2).
      cancel (sll_var_sub_list lis_pre (VarSub name t0 :: l0)).
    - unfold NULL in *; split_pures; dump_pre_spatial; try reflexivity; try assumption.
  + unfold termtypeID in PreH3; congruence.
Qed.

Lemma proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sub_thm_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_sub_thm_return_wit_2_split_goal_spatial : sub_thm_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH11, PreH8.
  sep_apply sll_var_sub_list_fold; [ | unfold NULL; lia | unfold NULL; lia].
  rewrite PreH7.
  sep_apply store_sub_thm_res_fold; [ | unfold NULL; lia].
  cancel.
Qed.

Lemma proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sub_thm_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_sub_thm_return_wit_3_split_goal_spatial : sub_thm_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  unfold sll_var_sub_list.
  pose proof (sll_zero store_var_sub_cell "var_sub_list" "next" 0 l) as Hzero.
  unfold NULL in Hzero.
  assert (0=0) as Hz. {reflexivity. }
  pose proof Hzero Hz as Hsll.
  destruct l.
  + simpl.
    unfold store_sub_thm_res.
    pose proof thm_subst_nil t as Hnil; rewrite Hnil.
    unfold store_partial_quant.
    split_pure_spatial.
    - Intros_p Hnull.
      cancel (store_term thm_pre t).
    - split_pures; dump_pre_spatial; try reflexivity.
  + apply sll_zero_right; discriminate.
Qed.

Lemma proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sub_thm_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_1 : sub_thm_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string.
  Intros n1 n2.
  dump_pre_spatial.
  assumption.
Qed.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_2 : sub_thm_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string.
  Intros n1 n2.
  dump_pre_spatial.
  assumption.
Qed.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_3 : sub_thm_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string.
  Intros n1 n2.
  dump_pre_spatial.
  assumption.
Qed.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_1.
  + Goal_apply proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_2.
  + Goal_apply proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_3.
Qed. 

Lemma proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  assert (lis <> NULL) as Hlis_nonnull by (unfold NULL in *; lia).
  pose proof sll_not_zero store_var_sub_cell "var_sub_list" "next" lis l Hlis_nonnull as Hsll_nonzero.
  unfold sll_var_sub_list.
  sep_apply Hsll_nonzero.
  unfold store_var_sub_cell at 1.
  Intros y a l0 y0.
  Exists y y0 a l0.
  split_pure_spatial.
  - cancel (&( thm # "term" ->ₛ "type") # Int |-> termtypeID t).
    cancel (store_term' thm t).
    cancel (&( lis # "var_sub_list" ->ₛ "cur") # Ptr |-> y0).
    cancel (store_var_sub y0 a).
    cancel (&( lis # "var_sub_list" ->ₛ "next") # Ptr |-> y).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold NULL in H.
      exact H.
    + dump_pre_spatial.
      exact H0.
Qed. 

Lemma proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Quant; [ | auto | auto ].
  Intros qtype qvar body y z.
  destruct vs.
  unfold store_var_sub.
  Intros sy sz.
  Exists sz sy z y name.
  Exists t0 qtype qvar body.
  split_pure_spatial.
  - cancel (&( lis # "var_sub_list" ->ₛ "cur") # Ptr |-> lis_cur).
    cancel (&( thm # "term" ->ₛ "type") # Int |-> termtypeID t).
    cancel (&( thm # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype).
    cancel (&( thm # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y).
    cancel (&( thm # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z).
    cancel (store_string y qvar).
    cancel (store_term z body).
    cancel (&( lis_cur # "var_sub" ->ₛ "var") # Ptr |-> sy).
    cancel (&( lis_cur # "var_sub" ->ₛ "sub_term") # Ptr |-> sz).
    cancel (store_string sy name).
    cancel (store_term sz t0).
  - split_pures; dump_pre_spatial.
    + unfold NULL in H0.
      exact H0.
    + unfold NULL in H3.
      exact H3.
    + exact H1.
    + reflexivity.
Qed. 

Lemma proof_of_separate_imply_return_wit_1_split_goal_spatial : separate_imply_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH18.
  rewrite PreH15.
  rewrite PreH12.
  unfold store_imply_res.
  unfold sep_impl.
  unfold ctID in PreH11.
  destruct llctype; try lia.
  Exists t1' t2'.
  sep_apply (store_term_const_fold_order__implication_returns v_4 CImpl llcctnt PreH14).
  sep_apply (store_term_apply_fold_order__implication_returns v_2 v_4 v_3 (TermConst CImpl llcctnt) lr PreH17).
  sep_apply (store_term_apply_fold_order__implication_returns t_pre v_2 v (TermApply (TermConst CImpl llcctnt) lr) rt PreH20).
  cancel.
Qed.

Lemma proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_separate_imply_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_separate_imply_return_wit_2_split_goal_spatial : separate_imply_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH18.
  unfold store_term at 3.
  fold store_term.
  Exists v_2 v.
  rewrite PreH15.
  rewrite PreH12.
  sep_apply (store_term_const_fold_order__implication_returns v_4 llctype llcctnt PreH14).
  sep_apply (store_term_apply_fold_order__implication_returns v_2 v_4 v_3 (TermConst llctype llcctnt) lr PreH17).
  unfold store_imply_res.
  unfold sep_impl.
  destruct llctype.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - unfold ctID in PreH11; contradiction.
Qed.

Lemma proof_of_separate_imply_return_wit_2 : separate_imply_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_separate_imply_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_separate_imply_return_wit_3_split_goal_spatial : separate_imply_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH12.
  unfold store_term at 3.
  fold store_term.
  rewrite PreH9.
  unfold store_term at 3.
  fold store_term.
  Exists v_2 v v_4 v_3.
  sep_apply ((store_term_fold_out v_4 ll) PreH8).
  unfold store_imply_res.
  unfold sep_impl.
  destruct ll.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try lia.
  - unfold termtypeID in PreH7; contradiction.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try lia.
  - split_pure_spatial.
    + cancel.
    + unfold NULL in *; split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_separate_imply_return_wit_3 : separate_imply_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_separate_imply_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_separate_imply_return_wit_4_split_goal_spatial : separate_imply_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH7.
  unfold store_term at 2.
  fold store_term.
  Exists v_2 v.
  sep_apply ((store_term_fold_out v_2 lt) PreH6).
  unfold store_imply_res.
  unfold sep_impl.
  destruct lt.
  - split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      * unfold NULL in PreH9.
        exact PreH9.
      * unfold NULL.
        reflexivity.
  - split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      * unfold NULL in PreH9.
        exact PreH9.
      * unfold NULL.
        reflexivity.
  - unfold termtypeID in PreH5; contradiction.
  - split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      * unfold NULL in PreH9.
        exact PreH9.
      * unfold NULL.
        reflexivity.
Qed.

Lemma proof_of_separate_imply_return_wit_4 : separate_imply_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_separate_imply_return_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_separate_imply_return_wit_5_split_goal_spatial : separate_imply_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_imply_res.
  unfold sep_impl.
  destruct trm as [var | ctype content | lt rt | qtype qvar body]; unfold NULL in *.
  - sep_apply ((store_term_fold_out t_pre (TermVar var)) PreH4).
    split_pure_spatial.
    + cancel (store_term t_pre (TermVar var)).
    + split_pures; dump_pre_spatial; try reflexivity.
  - sep_apply ((store_term_fold_out t_pre (TermConst ctype content)) PreH4).
    split_pure_spatial.
    + cancel (store_term t_pre (TermConst ctype content)).
    + split_pures; dump_pre_spatial; try reflexivity.
  - unfold termtypeID in PreH3; contradiction.
  - sep_apply ((store_term_fold_out t_pre (TermQuant qtype qvar body)) PreH4).
    split_pure_spatial.
    + cancel (store_term t_pre (TermQuant qtype qvar body)).
    + split_pures; dump_pre_spatial; try reflexivity.
Qed.

Lemma proof_of_separate_imply_return_wit_5 : separate_imply_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_separate_imply_return_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_separate_imply_which_implies_wit_1_split_goal_1 : separate_imply_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hnonnull.
  dump_pre_spatial.
  unfold NULL in Hnonnull.
  exact Hnonnull.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_1_split_goal_spatial : separate_imply_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hnonnull.
  cancel.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_separate_imply_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_separate_imply_which_implies_wit_1_split_goal_1.
Qed. 

Lemma proof_of_separate_imply_which_implies_wit_2 : separate_imply_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Apply; unfold NULL in *.
  Intros lt rt y z.
  Exists z y lt rt.
  match goal with
  | Heq : trm = TermApply lt rt |- _ => rewrite Heq
  end.
  split_pure_spatial.
  - cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
    cancel (store_term y lt).
    cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
    cancel (store_term z rt).
  - dump_pre_spatial; reflexivity.
  - unfold NULL; exact PreH1.
  - exact PreH2.
Qed. 

Lemma proof_of_separate_imply_which_implies_wit_3_split_goal_1 : separate_imply_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hnonnull.
  dump_pre_spatial.
  unfold NULL in Hnonnull.
  exact Hnonnull.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_3_split_goal_spatial : separate_imply_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hnonnull.
  cancel.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hv.
  unfold NULL in Hv.
  split_pure_spatial.
  - cancel. cancel.
  - split_pures; dump_pre_spatial.
    exact Hv.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_4 : separate_imply_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Apply; unfold NULL in *.
  Intros ll lr y z.
  Exists z y ll lr.
  split_pure_spatial.
  + cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> v).
    cancel (&( v # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
    cancel (store_term y ll).
    cancel (&( v # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
    cancel (store_term z lr).
  + split_pures; dump_pre_spatial; assumption.
  + unfold NULL in *; exact PreH1.
  + exact PreH2.
Qed. 

Lemma proof_of_separate_imply_which_implies_wit_5_split_goal_1 : separate_imply_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hv.
  unfold NULL in Hv; entailer!.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_5_split_goal_spatial : separate_imply_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hnonnull.
  cancel.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_separate_imply_which_implies_wit_5_split_goal_spatial.
  - Goal_apply proof_of_separate_imply_which_implies_wit_5_split_goal_1.
Qed. 

Lemma proof_of_separate_imply_which_implies_wit_6 : separate_imply_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term'_Const; unfold NULL in *.
  Intros ty ct.
  Exists ty ct.
  match goal with
  | Heq : ll = TermConst ty ct |- _ => rewrite <- Heq
  end.
  split_pure_spatial.
  - cancel (&( t # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> v).
    cancel (&( v # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> v_2).
    cancel (&( v_2 # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ty).
    cancel (&( v_2 # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> ct).
  - dump_pre_spatial; reflexivity.
  - unfold NULL in *; exact PreH1.
  - exact PreH2.
Qed. 

Lemma proof_of_check_list_gen_entail_wit_1 : check_list_gen_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists theo_low_level_spec nil.
  split_pure_spatial.
  - unfold sllbseg_term_list, sllbseg.
    split_pure_spatial.
    + cancel (store_term thm_pre theo_low_level_spec).
      cancel (store_term target_pre targ_low_level_spec).
    + dump_pre_spatial; reflexivity.
  - dump_pre_spatial.
    exact PreH1.
Qed. 

Lemma proof_of_check_list_gen_entail_wit_2 : check_list_gen_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists tr (l_2 ++ (r::nil)).
  split_pure_spatial.
  - sep_apply (store_term_cell_fold retval pa r); [ | exact PreH2].
    sep_apply (sllbseg_one r tail_ptr retval); [ | exact PreH2].
    unfold sllbseg_term_list.
    sep_apply (sllbseg_sllbseg store_term_cell "term_list" "next"
      (&("check_list")) tail_ptr (&(retval # "term_list" ->ₛ "next")) l_2 (r::nil)).
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    rewrite PreH4 in PreH5.
    subst.
    unfold check_from_mid_rel in PreH6 at 1.
    prog_nf in PreH6.
    unfold_loop in PreH6.
    prog_nf in PreH6.
    unfold check_list_gen_body in PreH6 at 1.
    prog_nf in PreH6.
    unfold term_alpha_eqn in PreH5.
    destruct term_alpha_eq eqn:Heq; [lia | ].
    cbn [sep_impl] in PreH6.
    prog_nf in PreH6.
    exact PreH6.
Qed. 

Lemma proof_of_check_list_gen_return_wit_1 : check_list_gen_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists t_2 l_2.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold term_alpha_eqn in PreH2.
    destruct (term_alpha_eq t_2 targ_low_level_spec) eqn:Heq; [ | congruence].
    unfold check_from_mid_rel in PreH3 at 1.
    prog_nf in PreH3.
    rewrite (repeat_break_unfold _ _) in PreH3.
    prog_nf in PreH3.
    unfold check_list_gen_body in PreH3 at 1.
    rewrite Heq in PreH3.
    prog_nf in PreH3.
    exact PreH3.
Qed. 

Lemma proof_of_check_list_gen_return_wit_2 : check_list_gen_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst retval_2.
  sep_apply (store_imply_res_zero t_2).
  Intros_p Hnone.
  Intros_p Hnull.
  Exists t_2 (@nil term).
  split_pure_spatial.
  - unfold sll_term_list; simpl.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial; reflexivity.
  - dump_pre_spatial.
    unfold term_alpha_eqn in PreH3.
    destruct (term_alpha_eq t_2 targ_low_level_spec) eqn:Heq; [congruence | ].
    unfold check_from_mid_rel in PreH4 at 1.
    prog_nf in PreH4.
    rewrite (repeat_break_unfold _ _) in PreH4.
    prog_nf in PreH4.
    unfold check_list_gen_body in PreH4 at 1.
    rewrite Heq, Hnone in PreH4.
    prog_nf in PreH4.
    exact PreH4.
Qed. 

Lemma proof_of_check_list_gen_which_implies_wit_1 : check_list_gen_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply sllbseg_2_sllseg_term.
  Intros c.
  Exists c.
  cancel.
Qed. 

Lemma proof_of_check_list_gen_which_implies_wit_2 : check_list_gen_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_imply_res.
  destruct (sep_impl ttm) eqn:Heq.
  2: {
    Intros_p Hnull.
    unfold NULL in *; contradiction.
  }
  destruct i.
  Intros y z.
  unfold sep_impl in Heq.
  destruct ttm eqn:Heq1; try congruence.
  destruct t1 eqn:Heq11; try congruence.
  destruct t3 eqn:Heq111; try congruence.
  destruct ctype eqn:Hc; try congruence.
  unfold store_ImplyProp.
  Intros_p Hp.
  Exists z y content t4 t2.
  inversion Heq; subst.
  split_pure_spatial.
  - cancel (&( p # "imply_prop" ->ₛ "assum") # Ptr |-> y).
    cancel (&( p # "imply_prop" ->ₛ "concl") # Ptr |-> z).
    cancel (store_term y assum).
    cancel (store_term z concl).
  - dump_pre_spatial; subst; reflexivity.
Qed. 

Lemma proof_of_check_list_gen_which_implies_wit_3_split_goal_spatial : check_list_gen_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_ImplyProp.
  split_pure_spatial.
  - sepcon_right_assoc; cancel.
  - dump_pre_spatial. unfold NULL in *; exact PreH1.
Qed.

Lemma proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_list_gen_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_check_list_gen_which_implies_wit_4 : check_list_gen_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply sllbseg_2_sllseg_term.
  Intros c.
  Exists c.
  cancel.
Qed. 

Lemma proof_of_thm_apply_return_wit_1 : thm_apply_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_2.
  unfold store_sub_thm_res.
  destruct (thm_subst_allres t_implementation l_implementation)
    as [[prefix body] |] eqn:Hnone.
  - sep_apply (store_term_unfold 0 body).
    Intros_p Hzero.
    unfold NULL in Hzero.
    contradiction.
  - Intros_p Hzero.
    Exists (thm_subst' t_implementation l_implementation) (SRBool 0).
    unfold store_solve_res, restypeID.
    split_pure_spatial.
    + repeat rewrite <- sepcon_right_assoc.
      repeat cancel.
    + split_pures; dump_pre_spatial.
      * unfold thm_app_rel in PreH6.
        cbn [thm_app] in PreH6.
        rewrite Hnone in PreH6.
        exact PreH6.
      * unfold NULL; exact PreH4.
Qed. 

Lemma proof_of_thm_apply_return_wit_2 : thm_apply_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcombine : forall (prefix : partial_quant) (root finish : Z) (body : term),
    store_partial_quant root finish prefix ** store_term finish body |--
      EX result, store_term root result).
  { induction prefix as [|qt x prefix IH]; intros root finish body.
    - unfold store_partial_quant at 1; fold store_partial_quant. Intros_p Heq. subst root.
      Exists body. repeat rewrite <- sepcon_right_assoc; cancel.
    - unfold store_partial_quant at 1; fold store_partial_quant. Intros y z.
      sep_apply (IH z finish body). Intros result.
      Exists (TermQuant qt x result).
      unfold store_term; fold store_term. unfold termtypeID. Exists y z.
      split_pure_spatial; [repeat cancel | dump_pre_spatial; assumption]. }
  sep_apply (Hcombine pq thm_pre retval_2 st).
  Intros t.
  Exists t (SRBool 1).
  unfold store_solve_res, restypeID.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial.
    + unfold thm_app_rel in PreH8.
      cbn [thm_app] in PreH8.
      unfold thm_subst_allres_rel in PreH2.
      rewrite PreH2 in PreH8.
      unfold term_alpha_eqn in PreH1.
      destruct (term_alpha_eq st g_implementation); [exact PreH8 | congruence].
    + unfold NULL; exact PreH6.
Qed. 

Lemma proof_of_thm_apply_return_wit_3 : thm_apply_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcombine : forall (prefix : partial_quant) (root finish : Z) (body : term),
    store_partial_quant root finish prefix ** store_term finish body |--
      EX result, store_term root result).
  { induction prefix as [|qt x prefix IH]; intros root finish body.
    - unfold store_partial_quant at 1; fold store_partial_quant. Intros_p Heq. subst root.
      Exists body. repeat rewrite <- sepcon_right_assoc; cancel.
    - unfold store_partial_quant at 1; fold store_partial_quant. Intros y z.
      sep_apply (IH z finish body). Intros result.
      Exists (TermQuant qt x result).
      unfold store_term; fold store_term. unfold termtypeID. Exists y z.
      split_pure_spatial; [repeat cancel | dump_pre_spatial; assumption]. }
  sep_apply (Hcombine pq thm_pre retval_2 st).
  Intros t.
  Exists t (SRTList l).
  unfold store_solve_res, restypeID. Exists retval_5.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial.
    + exact PreH1.
    + unfold NULL; exact PreH9.
Qed. 

Lemma proof_of_thm_apply_which_implies_wit_1_split_goal_spatial : thm_apply_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_thm_apply_which_implies_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_sub_thm_res.
  destruct (thm_subst_allres t_implementation l_implementation)
    as [[pq st] |] eqn:Heq.
  - Exists pq st.
    split_pure_spatial.
    + repeat cancel.
    + dump_pre_spatial. unfold thm_subst_allres_rel. exact Heq.
  - Intros_p Hzero. contradiction.
Qed. 

Lemma proof_of_thm_apply_which_implies_wit_3_split_goal_spatial : thm_apply_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  rewrite store_solve_res'_equiv.
  sepcon_right_assoc; cancel.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_thm_apply_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_thm_apply_which_implies_wit_4_split_goal_1 : thm_apply_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold thm_app_rel in PreH3.
  cbn [thm_app] in PreH3.
  unfold thm_subst_allres_rel in PreH2.
  rewrite PreH2 in PreH3.
  unfold term_alpha_eqn in PreH1.
  destruct (term_alpha_eq st g_implementation); [congruence | exact PreH3].
Qed.

Lemma proof_of_thm_apply_which_implies_wit_4 : thm_apply_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_thm_apply_which_implies_wit_4_split_goal_1.
Qed. 

Lemma proof_of_thm_apply_implementation_entail_high_level_spec : thm_apply_implementation_entail_high_level_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists t_high_level_spec l_high_level_spec g_high_level_spec
    (fun sr (_ : unit) => sr = thm_app_result t_high_level_spec l_high_level_spec g_high_level_spec).
  split_pure_spatial.
  - cancel (store_term thm_pre t_high_level_spec).
    cancel (sll_var_sub_list lis_pre l_high_level_spec).
    cancel (store_term goal_pre g_high_level_spec).
    Intros_r retval.
    apply derivable1_wand_sepcon_adjoint.
    Intros t sr.
    unfold safeExec, safe in H.
    destruct H as [s [_ Hresult]].
    rewrite wp_ret in Hresult.
    change (sr = thm_app_result t_high_level_spec l_high_level_spec g_high_level_spec) in Hresult.
    subst sr.
    Exists t.
    repeat cancel.
  - split_pures.
    + sep_apply_l_atomic (store_term_unfold thm_pre t_high_level_spec).
      Intros_p Hnonnull.
      dump_pre_spatial. exact Hnonnull.
    + dump_pre_spatial.
      unfold safeExec, safe.
      exists tt. split; [exact I |].
      unfold weakestpre.
      intros sr s Hrun.
      exact (thm_app_result_correct t_high_level_spec l_high_level_spec g_high_level_spec tt sr s I Hrun).
Qed.

Lemma proof_of_check_list_gen_low_level_spec_entail_low_level_spec_aux : check_list_gen_low_level_spec_entail_low_level_spec_aux.
Proof.
  unfold check_list_gen_low_level_spec_entail_low_level_spec_aux.
  intros B thm_pre target_pre theo_low_level_spec_aux targ_low_level_spec_aux c_low_level_spec_aux X_low_level_spec_aux.
  LLM_pre_process ltac:(int_auto).
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists theo_low_level_spec_aux targ_low_level_spec_aux X'.
  split_pure_spatial.
  - cancel (store_term thm_pre theo_low_level_spec_aux).
    cancel (store_term target_pre targ_low_level_spec_aux).
    Intros_r retval.
    apply derivable1_wand_sepcon_adjoint.
    Intros t2 l2; Exists t2 l2.
    split_pure_spatial.
    + repeat cancel.
    + dump_pre_spatial.
      apply H0.
      exact H1.
  - dump_pre_spatial; assumption.
Qed. 

