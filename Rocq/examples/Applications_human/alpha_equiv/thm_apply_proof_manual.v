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
From SimpleC.EE.Applications_human.alpha_equiv Require Import thm_apply_goal.
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

Lemma sllbseg_seg: forall x y z l1 l2,
  sllbseg_term_list x y l1 **
  sllbseg_term_list y z l2 |--
  sllbseg_term_list x z (l1++l2).
Proof.
  intros.
  revert x; induction l1; simpl; intros.
  + Intros.
    subst x.
    cancel.
  + Intros u.
    Exists u.
    sep_apply (IHl1 (&( u # "term_list" ->ₛ "next"))).
    split_pure_spatial.
    - cancel (x # Ptr |-> u).
      cancel (store_term_cell u a).
      cancel (sllbseg_term_list &( u # "term_list" ->ₛ "next") z (l1 ++ l2)).
    - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma sllbseg_one_app: forall a l x y z retval,
  retval <> NULL ->
  sllbseg_term_list x y l **
  y # Ptr |-> retval **
  &(retval # "term_list" ->ₛ "element") # Ptr |-> z **
  store_term z a |--
  sllbseg_term_list x &(retval # "term_list" ->ₛ "next") (l++(a::nil)).
Proof.
  intros.
  sep_apply (store_term_cell_fold retval z a); [ | auto].
  sep_apply sllbseg_one; [ | auto].
  sep_apply (sllbseg_seg x y &( retval # "term_list" ->ₛ "next") l (a :: nil)).
  cancel.
Qed.

Lemma store_term_const_fold_order: forall x ctype content,
  x <> 0 ->
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content **
  &(x # "term" ->ₛ "type") # Int |-> termtypeID (TermConst ctype content)
  |-- store_term x (TermConst ctype content).
Proof.
  intros.
  unfold store_term, store_term', NULL.
  simpl.
  split_pure_spatial.
  - cancel (&( x # "term" ->ₛ "type") # Int |-> 1).
    cancel (&( x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype).
    cancel (&( x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content).
  - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma store_term_apply_fold_order: forall x y z lt rt,
  x <> 0 ->
  &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
  store_term y lt **
  &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
  store_term z rt **
  &(x # "term" ->ₛ "type") # Int |-> termtypeID (TermApply lt rt)
  |-- store_term x (TermApply lt rt).
Proof.
  intros.
  unfold store_term, store_term', NULL.
  simpl.
  Exists y z.
  split_pure_spatial.
  - cancel (&( x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
    cancel (&( x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
    cancel (store_term y lt).
    cancel (store_term z rt).
    cancel (&( x # "term" ->ₛ "type") # Int |-> 2).
  - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_sub_thm_return_wit_3_split_goal_spatial :
  sub_thm_return_wit_3_split_goal_spatial.
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

Lemma proof_of_sub_thm_return_wit_2_split_goal_spatial :
  sub_thm_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH12, PreH8.
  sep_apply sll_var_sub_list_fold; [ | unfold NULL; lia | unfold NULL; lia].
  rewrite PreH5.
  sep_apply store_sub_thm_res_fold; [ | unfold NULL; lia].
  rewrite PreH9.
  cancel.
Qed.

Lemma proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sub_thm_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_sub_thm_return_wit_1_split_goal_spatial :
  sub_thm_return_wit_1_split_goal_spatial.
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

Lemma proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_1 :
  sub_thm_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string.
  Intros n1 n2.
  dump_pre_spatial.
  assumption.
Qed.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_2 :
  sub_thm_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string.
  Intros n1 n2.
  dump_pre_spatial.
  assumption.
Qed.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure_split_goal_3 :
  sub_thm_partial_solve_wit_3_pure_split_goal_3.
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

Lemma proof_of_separate_imply_return_wit_5_split_goal_spatial :
  separate_imply_return_wit_5_split_goal_spatial.
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

Lemma proof_of_separate_imply_return_wit_4_split_goal_spatial :
  separate_imply_return_wit_4_split_goal_spatial.
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

Lemma proof_of_separate_imply_return_wit_3_split_goal_spatial :
  separate_imply_return_wit_3_split_goal_spatial.
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

Lemma proof_of_separate_imply_return_wit_2_split_goal_spatial :
  separate_imply_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH18.
  unfold store_term at 3.
  fold store_term.
  Exists v_2 v.
  rewrite PreH15.
  rewrite PreH12.
  sep_apply (store_term_const_fold_order v_4 llctype llcctnt PreH14).
  sep_apply (store_term_apply_fold_order v_2 v_4 v_3 (TermConst llctype llcctnt) lr PreH17).
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

Lemma proof_of_separate_imply_return_wit_1_split_goal_spatial :
  separate_imply_return_wit_1_split_goal_spatial.
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
  sep_apply (store_term_const_fold_order v_4 CImpl llcctnt PreH14).
  sep_apply (store_term_apply_fold_order v_2 v_4 v_3 (TermConst CImpl llcctnt) lr PreH17).
  sep_apply (store_term_apply_fold_order t_pre v_2 v (TermApply (TermConst CImpl llcctnt) lr) rt PreH20).
  cancel.
Qed.

Lemma proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_separate_imply_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Ht.
  unfold NULL in Ht.
  split_pure_spatial.
  cancel.
  dump_pre_spatial.
  exact Ht.
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

Lemma proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hv.
  unfold NULL in Hv.
  split_pure_spatial.
  - cancel.
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

Lemma proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_term_unfold.
  Intros_p Hv.
  unfold NULL in Hv.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    exact Hv.
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
  - sep_apply sllbseg_one_app; [cancel | auto].
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    rewrite PreH4 in PreH5.
    subst.
    unfold check_from_mid_rel in *.
    rewrite (repeat_break_unfold _ _) in PreH6.
    prove_by_one_abs_step (by_continue (tr, targ_low_level_spec, l_2 ++ r :: nil)).
    unfold check_list_gen_body.
    unfold term_alpha_eqn in PreH5.
    destruct term_alpha_eq; [ lia | ].
    unfold sep_impl.
    abs_ret_step.
Qed.

Lemma proof_of_check_list_gen_return_wit_2 : check_list_gen_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH3.
  rewrite PreH1.
  subst.
  sep_apply store_imply_res_zero.
  Intros_p Hnone.
  Intros_p Hzero.
  Exists t_2 nil.
  unfold sll_term_list.
  simpl.
  split_pure_spatial.
  - cancel (store_term target_pre targ_low_level_spec).
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold check_from_mid_rel in *.
    rewrite (repeat_break_unfold _ _) in PreH4.
    prove_by_one_abs_step (by_break (makepair t_2 nil)).
    unfold check_list_gen_body.
    unfold term_alpha_eqn in PreH3.
    destruct term_alpha_eq eqn:Heq; [ congruence | ].
    rewrite Hnone.
    abs_ret_step.
Qed.

Lemma proof_of_check_list_gen_return_wit_1 : check_list_gen_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists t_2 l_2.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold check_from_mid_rel in *.
    rewrite (repeat_break_unfold _ _) in PreH3.
    prove_by_one_abs_step (by_break (makepair t_2 l_2)).
    unfold check_list_gen_body.
    unfold term_alpha_eqn in PreH2.
    destruct term_alpha_eq eqn:Heq; [ | congruence].
    abs_ret_step.
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

Lemma proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_ImplyProp.
  split_pure_spatial.
  - cancel (&( p # "imply_prop" ->ₛ "assum") # Ptr |-> pa).
    cancel (&( p # "imply_prop" ->ₛ "concl") # Ptr |-> pc).
    cancel (store_term pa r).
    cancel (store_term pc tr).
  - dump_pre_spatial.
    unfold NULL in *; exact PreH1.
Qed.

Lemma proof_of_check_list_gen_which_implies_wit_4 : check_list_gen_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply sllbseg_2_sllseg_term.
  Intros c.
  Exists c.
  cancel.
Qed.

Lemma partial_quant_not_zero : forall z retval p st, 
  store_partial_quant z retval p ** store_term retval st |-- “ z <> 0 ”.
Proof.
  intros.
  destruct p; simpl in *.
  - Intros_p Heq.
    sep_apply store_term_unfold.
    Intros_p Hret.
    subst z.
    unfold NULL in Hret.
    dump_pre_spatial.
    exact Hret.
  - Intros y z0.
    unfold NULL in H.
    dump_pre_spatial.
    exact H.
Qed.

Lemma partial_quant_combine: forall t l pq st retval thm_pre,
  thm_pre <> 0 ->
  thm_subst_allres t l = Some (pq, st) ->
      store_term retval st ** store_partial_quant thm_pre retval pq
      |-- store_term thm_pre (thm_subst' t l).
Proof.
  intros. revert H H0. revert t pq st thm_pre.
  induction l ; intros ; simpl in *.
  + inversion H0.
    subst. simpl. Intros. subst. cancel.
  + destruct a.  
    destruct t ; simpl in * ; try congruence.
    destruct (thm_subst_allres (term_subst_t t0 name t) l) eqn:Heq; [ | congruence].
    destruct p.
    inversion H0; subst. simpl.
    Intros y z; Exists y z.
    split_pure_spatial.
    - prop_apply partial_quant_not_zero.
      Intros.
      sep_apply (IHl (term_subst_t t0 name t) p st z); try auto.
      cancel.
    - unfold NULL in H.
      dump_pre_spatial.
      exact H.
Qed.

Lemma store_sub_thm_res_zero: forall thm_pre t_2 l,
  store_sub_thm_res thm_pre 0 t_2 l |-- “ thm_subst_allres t_2 l = None ” && store_term thm_pre (thm_subst' t_2 l).
Proof.
  intros.
  unfold store_sub_thm_res.
  destruct thm_subst_allres eqn:Heq.
  + destruct p.
  sep_apply (store_null_right t (store_partial_quant thm_pre 0 p)
      (“ Some (p, t) = None ” && store_term thm_pre (thm_subst' t_2 l))
  ).
  cancel.
  + split_pure_spatial.
    - Intros_p Hz.
      cancel.
    - dump_pre_spatial; reflexivity.
Qed. 

Lemma proof_of_thm_apply_return_wit_3 : thm_apply_return_wit_3.
Proof. 
  LLM_pre_process ltac:(int_auto).
  Exists (thm_subst' t_2 l) (SRTList l_2).
  unfold thm_subst_allres_rel in PreH5.
  unfold store_solve_res.
  Exists retval_5.
  unfold restypeID.
  split_pure_spatial.
  - sep_apply (partial_quant_combine t_2 l pq st); [cancel | auto | auto].
  - split_pures.
    + dump_pre_spatial.
      match goal with
      | Hsafe : safeExec ATrue (applyf get_list (makepair _ l_2)) X |- _ =>
          unfold get_list in Hsafe; simpl in Hsafe; exact Hsafe
      end.
    + dump_pre_spatial.
      unfold NULL in *.
      match goal with
      | Hneq : retval <> 0 |- _ => exact Hneq
      end.
Qed.

Lemma proof_of_thm_apply_return_wit_2 : thm_apply_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (thm_subst' t_2 l) (SRBool 1).
  unfold store_solve_res, restypeID.
  unfold thm_subst_allres_rel in PreH2.
  split_pure_spatial.
  - sep_apply (partial_quant_combine t_2 l pq st); [cancel | auto | auto].
  - split_pures.
    + dump_pre_spatial.
      match goal with
      | Hsafe : safeExec ATrue (thm_app_rel t_2 l g) X,
        Hsubst : thm_subst_allres t_2 l = Some (pq, st),
        Halpha : retval_3 = term_alpha_eqn st g |- _ =>
          unfold thm_app_rel, thm_app in Hsafe;
          rewrite Hsubst in Hsafe;
          unfold term_alpha_eqn in Halpha;
          destruct term_alpha_eq eqn:Heq; [ exact Hsafe | congruence ]
      end.
    + dump_pre_spatial.
      unfold NULL in *.
      match goal with
      | Hneq : retval <> 0 |- _ => exact Hneq
      end.
Qed.

Lemma store_sub_thm_res_zero_late_unused: forall thm_pre t_2 l,
  store_sub_thm_res thm_pre 0 t_2 l |-- “ thm_subst_allres t_2 l = None ” && store_term thm_pre (thm_subst' t_2 l).
Proof.
  intros.
  apply store_sub_thm_res_zero.
Qed. 

Lemma proof_of_thm_apply_return_wit_1 : thm_apply_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (thm_subst' t_2 l) (SRBool 0).
  subst.
  sep_apply (store_sub_thm_res_zero thm_pre t_2 l).
  Intros_p Hnone.
  unfold store_solve_res, restypeID.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      match goal with
      | Hsafe : safeExec ATrue (thm_app_rel t_2 l g) X |- _ =>
          unfold thm_app_rel, thm_app in Hsafe;
          rewrite Hnone in Hsafe;
          exact Hsafe
      end.
    + dump_pre_spatial.
      unfold NULL in *.
      match goal with
      | Hneq : retval <> 0 |- _ => exact Hneq
      end.
Qed.

(* Already exported by thm_apply_proof_auto.v.
Lemma proof_of_thm_apply_partial_solve_wit_8_pure : thm_apply_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)


Lemma proof_of_thm_apply_which_implies_wit_1_split_goal_spatial :
  thm_apply_which_implies_wit_1_split_goal_spatial.
Proof. 
  unfold thm_apply_which_implies_wit_1_split_goal_spatial.
  intros.
  unfold store_solve_res.
  unfold restypeID.
  Intros_p Hres.
  cancel.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_thm_apply_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_sub_thm_res.
  destruct (thm_subst_allres t l) eqn:Heq.
  - destruct p.
    Exists p t0.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      unfold thm_subst_allres_rel.
      exact Heq.
  - Intros.
    contradiction.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_3_split_goal_spatial :
  thm_apply_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  rewrite store_solve_res'_equiv.
  cancel.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_thm_apply_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_4_split_goal_1 :
  thm_apply_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold thm_app_rel, thm_app in PreH3.
  unfold thm_subst_allres_rel in PreH2.
  rewrite PreH2 in PreH3.
  unfold term_alpha_eqn in PreH1.
  destruct term_alpha_eq; [ congruence | ].
  unfold get_list in *.
  auto.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_4 : thm_apply_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_thm_apply_which_implies_wit_4_split_goal_1.
Qed.

Lemma proof_of_check_list_gen_derive_low_level_spec_aux_by_low_level_spec : check_list_gen_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists theo_low_level_spec_aux targ_low_level_spec_aux X'.
  split_pure_spatial.
  - cancel (store_term thm_pre theo_low_level_spec_aux).
    cancel (store_term target_pre targ_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros t2 l2 r2; Exists t2 l2 r2.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      apply H0.
      exact H1.
  - dump_pre_spatial; assumption.
Qed.
