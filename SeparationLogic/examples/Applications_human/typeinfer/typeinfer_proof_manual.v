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
From SimpleC.EE.Applications_human.typeinfer Require Import typeinfer_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.Applications_human.typeinfer Require Import typeinfer_lib.
From SimpleC.EE.Applications_human.typeinfer Require Import sound_pv.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_atype_unify_return_wit_5 : atype_unify_return_wit_5.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
  rewrite PreH6.
  exact PreH2.
Qed.

Lemma proof_of_atype_unify_return_wit_6 : atype_unify_return_wit_6.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
Qed.

Lemma to_aux : forall t1 tr1,
  store_type t1 tr1
  |-- EX t1_t : Z,
    &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
    store_type_aux t1 t1_t tr1.
Proof.
  pre_process.
  destruct tr1.
  + Exists 3.
    simpl store_type.
    unfold store_type_aux.
    entailer!.
  + Exists 0.
    simpl store_type.
    unfold store_type_aux.
    entailer!.
  + Exists 2.
    simpl store_type.
    unfold store_type_aux.
    Intros p1 p2.
    Exists p1 p2.
    entailer!.
  + Exists 1.
    simpl store_type.
    unfold store_type_aux.
    Intros p1 p2.
    Exists p1 p2.
    entailer!.
Qed.

Lemma from_aux : forall t1 tr1 t1_t,
    &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
    store_type_aux t1 t1_t tr1
  |-- store_type t1 tr1.
Proof.
  pre_process.
  destruct tr1.
  + simpl store_type_aux.
    unfold store_type.
    entailer!.
    subst.
    entailer!.
  + simpl store_type_aux.
    unfold store_type.
    entailer!.
    subst.
    entailer!.
  + simpl store_type_aux.
    simpl store_type.
    Intros p1 p2.
    Exists p1 p2.
    subst.
    entailer!.
  + simpl store_type_aux.
    simpl store_type.
    Intros p1 p2.
    Exists p1 p2.
    subst.
    entailer!.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_1 : atype_unify_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply to_aux.
  entailer!.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_2 : atype_unify_which_implies_wit_2.
Proof. 
  pre_process.
  subst.
  destruct tr1_verify.
  + entailer!.
    simpl store_type_aux.
    Exists n.
    entailer!.
  + unfold store_type_aux.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_3 : atype_unify_which_implies_wit_3.
Proof.
  pre_process.
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  2: unfold store_option_type; entailer!.
  Exists t.
  unfold solution_at.
  entailer!.
  Exists L.
  rename s_pre_verify into s.
  assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
    (store_option_type tp (Some t)) |-- (store_type_addr s) &( "res") n tp) as Haddr. {
    unfold store_type_addr.
    match goal with
    | Hsn : Some t = s n |- _ => rewrite <- Hsn
    end.
    entailer!; try lia.
  }
  sep_apply Haddr.
  rewrite (store_array_missing_i_merge_to_array _  (store_type_addr s) &( "res") n 100 tp L).
  2: auto.
  assert (L = replace_Znth n tp L) as Hreplace. {
    subst.
    rewrite replace_Znth_Znth.
    tauto.
  }
  rewrite Hreplace at 2.
  entailer!.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_4 : atype_unify_which_implies_wit_4.
Proof.
  pre_process.
  unfold store_solution_aux.
  unfold store_solution_aux.
  Intros L.
  rename s_pre_verify into s.
  destruct tr_opt.
  1: unfold store_option_type; entailer!.
  assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
    (store_option_type tp (None)) |-- (store_type_addr s) &( "res") n tp) as Haddr. {
    unfold store_type_addr.
    match goal with
    | Hsn : None = s n |- _ => rewrite <- Hsn
    end.
    entailer!; try lia.
  }
  unfold store_solution.
  Exists L.
  sep_apply Haddr.
  sep_apply (store_array_missing_i_merge_to_array _  (store_type_addr s) &( "res") n 100 tp L).
  2: auto.
  entailer!.
  + assert(
    (&( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
    &( t1 # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
    |-- store_type t1 tr1_verify
    ) as Htype. {
      subst.
      simpl store_type.
      entailer!.
    }
    sep_apply Htype.
    entailer!.
    assert (L = replace_Znth n tp L) as Hreplace. {
      subst.
      match goal with
      | Hz : ?v = Znth n L 100 |- _ => rewrite Hz
      | Hz : Znth n L 100 = ?v |- _ => rewrite <- Hz
      end.
      rewrite replace_Znth_Znth.
      tauto.
    }
    rewrite Hreplace at 2.
    entailer!.
  + assert(repr_rel_id s n (TVar n)). {
      eapply repr_rel_var; eauto.
    }
    match goal with
    | Heq : tr1_verify = TVar n |- _ => rewrite Heq
    end.
    eapply repr_rel_node_var; eauto.
Qed.

Lemma not_var_helper: forall t1 tr1 t1_t,
  t1_t <> 3 ->
  &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
  store_type_aux t1 t1_t tr1
  |-- “ not_var tr1 ” &&
      &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
      store_type_aux t1 t1_t tr1.
Proof.
  intros.
  destruct tr1.
  + simpl store_type_aux.
    entailer!.
  + entailer!.
  + entailer!.
  + entailer!.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_5 : atype_unify_which_implies_wit_5.
Proof.
  pre_process.
  sep_apply not_var_helper; auto.
  entailer!.
  sep_apply from_aux.
  entailer!.
  eapply repr_rel_node_not_var.
  tauto.
Qed.

Lemma proof_of_atype_unify1_return_wit_5 : atype_unify1_return_wit_5.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
  rewrite PreH6.
  exact PreH2.
Qed.

Lemma proof_of_atype_unify1_return_wit_6 : atype_unify1_return_wit_6.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_1 : atype_unify1_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply to_aux.
  entailer!.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_2 : atype_unify1_which_implies_wit_2.
Proof.
  pre_process.
  subst.
  destruct tr2.
  + entailer!.
    simpl store_type_aux.
    Exists n.
    entailer!.
  + unfold store_type_aux.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
Qed.


Lemma proof_of_atype_unify1_which_implies_wit_3 : atype_unify1_which_implies_wit_3.
Proof.
  pre_process.
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  2: unfold store_option_type; entailer!.
  Exists t.
  unfold solution_at.
  entailer!.
  Exists L.
  rename s_pre into s.
  assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
    (store_option_type tp (Some t)) |-- (store_type_addr s) &( "res") n tp) as Haddr. {
    unfold store_type_addr.
    match goal with
    | Hsn : Some t = s n |- _ => rewrite <- Hsn
    end.
    entailer!; try lia.
  }
  sep_apply Haddr.
  rewrite (store_array_missing_i_merge_to_array _  (store_type_addr s) &( "res") n 100 tp L).
  2: auto.
  assert (L = replace_Znth n tp L) as Hreplace. {
    subst.
    rewrite replace_Znth_Znth.
    tauto.
  }
  rewrite Hreplace at 2.
  entailer!.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_4 : atype_unify1_which_implies_wit_4.
Proof.
  pre_process.
  unfold store_solution_aux.
  unfold store_solution_aux.
  Intros L.
  rename s_pre into s.
  destruct tr_opt.
  1: unfold store_option_type; entailer!.
  assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
    (store_option_type tp (None)) |-- (store_type_addr s) &( "res") n tp) as Haddr. {
    unfold store_type_addr.
    match goal with
    | Hsn : None = s n |- _ => rewrite <- Hsn
    end.
    entailer!; try lia.
  }
  unfold store_solution.
  Exists L.
  sep_apply Haddr.
  sep_apply (store_array_missing_i_merge_to_array _  (store_type_addr s) &( "res") n 100 tp L).
  2: auto.
  entailer!.
  + assert(
    (&( t2 # "atype" ->ₛ "t") # Int |-> t2_t **
    &( t2 # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
    |-- store_type t2 tr2
    ) as Htype. {
      subst.
      simpl store_type.
      entailer!.
    }
    sep_apply Htype.
    entailer!.
    assert (L = replace_Znth n tp L) as Hreplace. {
      subst.
      match goal with
      | Hz : ?v = Znth n L 100 |- _ => rewrite Hz
      | Hz : Znth n L 100 = ?v |- _ => rewrite <- Hz
      end.
      rewrite replace_Znth_Znth.
      tauto.
    }
    rewrite Hreplace at 2.
    entailer!.
  + assert(repr_rel_id s n (TVar n)). {
      eapply repr_rel_var; eauto.
    }
    match goal with
    | Heq : tr2 = TVar n |- _ => rewrite Heq
    end.
    eapply repr_rel_node_var; eauto.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_5 : atype_unify1_which_implies_wit_5.
Proof.
  pre_process.
  sep_apply not_var_helper; auto.
  entailer!.
  sep_apply from_aux.
  entailer!.
  eapply repr_rel_node_not_var.
  tauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_13 : atype_unify2_return_wit_13.
Proof.
  pre_process.
  Exists s_pre.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_12 : atype_unify2_return_wit_12.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
  subst.
  apply (unify_rel_left_var s_pre tr1_prev n tr2_prev tr2);
  tauto.
Qed.


Lemma proof_of_atype_unify2_return_wit_11 : atype_unify2_return_wit_11.
Proof.
  pre_process.
  Exists s_pre.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_10 : atype_unify2_return_wit_10.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
  subst.
  eapply unify_rel_right_var; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_9 : atype_unify2_return_wit_9.
Proof.
  pre_process.
  Exists s_pre.
  entailer!.
  sep_apply from_aux.
  sep_apply from_aux.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_8 : atype_unify2_return_wit_8.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  simpl store_type.
  Exists t1_from t1_to.
  Exists t2_from t2_to.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_6 : atype_unify2_return_wit_6.
Proof.
  pre_process.
  Exists s_post_4.
  entailer!.
  subst.
  simpl store_type.
  Exists t1_from t1_to.
  Exists t2_from t2_to.
  entailer!.
  eapply unify_rel_arrow.
  - rewrite <- PreH6. exact PreH13.
  - rewrite <- PreH7. exact PreH14.
  - exact PreH5.
  - exact PreH2.
Qed.

Lemma proof_of_atype_unify2_return_wit_7 : atype_unify2_return_wit_7.
Proof.
  pre_process.
  Exists s_post_4.
  entailer!.
  subst.
  simpl store_type.
  Exists t1_from t1_to.
  Exists t2_from t2_to.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_5 : atype_unify2_return_wit_5.
Proof.
  pre_process.
  Exists s_post_3.
  entailer!.
  subst.
  simpl store_type.
  Exists t1_tfn t1_rand.
  Exists t2_tfn t2_rand.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_3 : atype_unify2_return_wit_3.
Proof.
  pre_process.
  Exists s_post_4.
  entailer!.
  subst.
  simpl store_type.
  Exists t1_tfn t1_rand.
  Exists t2_tfn t2_rand.
  entailer!.
  eapply unify_rel_apply.
  - rewrite <- PreH6. exact PreH14.
  - rewrite <- PreH7. exact PreH15.
  - exact PreH5.
  - exact PreH2.
Qed.

Lemma proof_of_atype_unify2_return_wit_4 : atype_unify2_return_wit_4.
Proof.
  pre_process.
  Exists s_post_4.
  entailer!.
  subst.
  simpl store_type.
  Exists t1_tfn t1_rand.
  Exists t2_tfn t2_rand.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_return_wit_2 : atype_unify2_return_wit_2.
Proof.
  pre_process.
  Exists s_pre.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
  subst.
  eapply unify_rel_atom; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_1 : atype_unify2_return_wit_1.
Proof.
  pre_process.
  Exists s_pre.
  entailer!.
  subst.
  unfold store_type.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_1 : atype_unify2_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply to_aux.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_2 : atype_unify2_which_implies_wit_2.
Proof.
  pre_process.
  subst.
  destruct tr1.
  + entailer!.
    simpl store_type_aux.
    Exists n.
    entailer!.
  + unfold store_type_aux.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_3 : atype_unify2_which_implies_wit_3.
Proof.
  pre_process.
  sep_apply to_aux.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_4 : atype_unify2_which_implies_wit_4.
Proof.
  pre_process.
  subst.
  destruct tr2.
  + entailer!.
    simpl store_type_aux.
    Exists n.
    entailer!.
  + unfold store_type_aux.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
  + unfold store_type_aux.
    Intros p1 p2.
    entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_5 : atype_unify2_which_implies_wit_5.
Proof.
  pre_process.
  entailer!.
  sep_apply from_aux.
  entailer!.
Qed.

Lemma helper_1 : forall t1 tr1,
  store_type_aux t1 1 tr1
  |-- EX (t1_to : Z) (tr1_to : TypeTree) (t1_from : Z) (tr1_from : TypeTree),
    “ tr1 = TArrow tr1_from tr1_to ” &&
    “ 1 = 1 ” &&
    &( t1 # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> t1_from **
    store_type t1_from tr1_from **
    &( t1 # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> t1_to **
    store_type t1_to tr1_to.
Proof.
  intros.
  destruct tr1; try simpl store_type_aux; try entailer!.
  + Intros p1 p2.
    entailer!.
  + Intros p1 p2.
    Exists p2 tr1_2 p1 tr1_1.
    entailer!.
Qed.

Lemma helper_2: forall t1 tr1,
  store_type_aux t1 2 tr1
  |-- EX (t1_tfn : Z) (tr1_tfn : TypeTree) (t1_rand : Z) (tr1_rand : TypeTree),
    “ tr1 = TApply tr1_tfn tr1_rand ” &&
    “ 2 = 2 ” &&
    &( t1 # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> t1_tfn **
    store_type t1_tfn tr1_tfn **
    &( t1 # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> t1_rand **
    store_type t1_rand tr1_rand.
Proof.
  intros.
  destruct tr1; try simpl store_type_aux; try entailer!.
  + Intros p1 p2.
    Exists p1 tr1_1 p2 tr1_2.
    entailer!.
  + Intros p1 p2.
    entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_6 : atype_unify2_which_implies_wit_6.
Proof.
  pre_process.
  subst.
  sep_apply helper_1.
  Intros t1_to tr1_to t1_from tr1_from.
  sep_apply helper_1.
  Intros t2_to tr2_to t2_from tr2_from.
  Exists tr2_to t2_to tr2_from t2_from.
  Exists tr1_to t1_to tr1_from t1_from.
  entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_7 : atype_unify2_which_implies_wit_7.
Proof.
  pre_process.
  subst.
  sep_apply helper_2.
  Intros t1_tfn tr1_tfn t1_rand tr1_rand.
  sep_apply helper_2.
  Intros t2_tfn tr2_tfn t2_rand tr2_rand.
  Exists tr2_rand t2_rand tr2_tfn t2_tfn.
  Exists tr1_rand t1_rand tr1_tfn t1_tfn.
  entailer!.
Qed.


Lemma last: forall t1 t1_t tr1,
  t1_t <> 3 -> t1_t <> 2 -> t1_t <> 1 ->
  &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
  store_type_aux t1 t1_t tr1
  |--
    EX (n : Z),
    “ t1_t = 0 ” &&
    “ tr1 = TAtom n ” &&
    &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
    &( t1 # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> n.
Proof.
  intros.
  destruct tr1.
  + simpl store_type_aux.
    entailer!.
  + simpl store_type_aux.
    entailer!.
    Exists n.
    entailer!.
  + simpl store_type_aux.
    Intros p1 p2.
    entailer!.
  + simpl store_type_aux.
    Intros p1 p2.
    entailer!.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_8 : atype_unify2_which_implies_wit_8.
Proof.
  pre_process.
  subst.
  sep_apply last; auto.
  Intros n.
  sep_apply last; auto.
  Intros m.
  Exists m n.
  entailer!.
Qed.


Lemma proof_of_atype_unify_derive_final_by_verify : 
  atype_unify_derive_final_by_verify.
Proof.
  pre_process.
  rename s_pre_final into s_cpre.
  unfold store_compressed_solution at 1.
  Intros s_pre.
  Exists s_pre tr1_final tr2_final.
  entailer!.
  pre_process_default.
  Split.
  - Intros s_post retval.
    pose proof (unify_soundness tr1_final tr2_final s_pre s_post s_cpre H H1 H0 H3).
    destruct H4 as [s_cpost ?].
    Left.
    Exists s_cpost retval.
    unfold store_compressed_solution.
    Exists s_post.
    entailer!.
  - Intros s_post retval.
    Right. 
    Exists s_post retval.
    entailer!.
Qed.
