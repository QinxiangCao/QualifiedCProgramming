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

Lemma proof_of_atype_unify_return_wit_5_split_goal_spatial :
  atype_unify_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify_return_wit_5 : atype_unify_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify_return_wit_6_split_goal_spatial :
  atype_unify_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify_return_wit_6 : atype_unify_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_return_wit_6_split_goal_spatial.
Qed.

Lemma to_aux : forall t1 tr1,
  store_type t1 tr1
  |-- EX t1_t : Z,
    &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
    store_type_aux t1 t1_t tr1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct tr1.
  + Exists 3.
    simpl store_type.
    unfold store_type_aux.
    Intros_p Hlo.
    Intros_p Hhi.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; try reflexivity; try lia.
  + Exists 0.
    simpl store_type.
    unfold store_type_aux.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; try reflexivity; assumption.
  + Exists 2.
    simpl store_type.
    unfold store_type_aux.
    Intros p1 p2.
    Exists p1 p2.
    split_pure_spatial.
    - cancel.
      cancel.
      cancel.
    - repeat split_pures; dump_pre_spatial; try reflexivity; assumption.
  + Exists 1.
    simpl store_type.
    unfold store_type_aux.
    Intros p1 p2.
    Exists p1 p2.
    split_pure_spatial.
    - cancel.
      cancel.
      cancel.
    - repeat split_pures; dump_pre_spatial; try reflexivity; assumption.
Qed.

Lemma from_aux : forall t1 tr1 t1_t,
    &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
    store_type_aux t1 t1_t tr1
  |-- store_type t1 tr1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct tr1.
  + simpl store_type_aux.
    unfold store_type.
    Intros_p Htag.
    Intros_p Hlo.
    Intros_p Hhi.
    rewrite Htag.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; try reflexivity; try lia.
  + simpl store_type_aux.
    unfold store_type.
    Intros_p Htag.
    rewrite Htag.
    cancel.
  + simpl store_type_aux.
    simpl store_type.
    Intros p1 p2.
    Exists p1 p2.
    rewrite H.
    cancel.
    cancel.
    cancel.
    cancel.
  + simpl store_type_aux.
    simpl store_type.
    Intros p1 p2.
    Exists p1 p2.
    rewrite H.
    cancel.
    cancel.
    cancel.
    cancel.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_1 : atype_unify_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply to_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_2 : atype_unify_which_implies_wit_2.
Proof. 
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct tr1_verify.
  + simpl store_type_aux.
    Exists n.
    Intros_p Htag.
    Intros_p Hlo.
    Intros_p Hhi.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; auto.
  + unfold store_type_aux.
    Intros_p Htag.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_3 : atype_unify_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  2: {
    unfold store_option_type.
    Intros_p Hnull.
    exfalso.
    unfold NULL in Hnull.
    lia.
  }
  Exists t.
  unfold solution_at.
  split_pure_spatial.
  - unfold store_solution.
    Exists L.
    rename s_pre_verify into s.
    assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
      (store_option_type tp (Some t)) |-- (store_type_addr s) &( "res") n tp) as Haddr. {
      unfold store_type_addr.
      match goal with
      | Hsn : Some t = s n |- _ => rewrite <- Hsn
      end.
      cancel.
    }
    sep_apply Haddr.
    cancel (&( t1 # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n).
    rewrite (store_array_missing_i_merge_to_array _  (store_type_addr s) &( "res") n 100 tp L).
    2: auto.
    assert (L = @replace_Znth addr n tp L) as Hreplace. {
      subst.
      rewrite replace_Znth_Znth.
      tauto.
    }
    rewrite Hreplace at 2.
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_4_split_goal_1 :
  atype_unify_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  - unfold store_option_type.
    Intros_p Hnonnull.
    exfalso.
    unfold NULL in Hnonnull.
    lia.
  -
    dump_pre_spatial.
    rewrite PreH9.
    eapply repr_rel_node_var.
    eapply repr_rel_var; eauto.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_4_split_goal_2 :
  atype_unify_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  - unfold store_option_type.
    Intros_p Hnonnull.
    exfalso.
    unfold NULL in Hnonnull.
    lia.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_4_split_goal_spatial :
  atype_unify_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  rename s_pre_verify into s.
  destruct tr_opt.
  - unfold store_option_type.
    Intros_p Hnonnull.
    exfalso.
    unfold NULL in Hnonnull.
    lia.
  - assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
      store_option_type tp None |-- (store_type_addr s) &( "res") n tp) as Haddr. {
      unfold store_type_addr.
      match goal with
      | Hsn : None = s n |- _ => rewrite <- Hsn
      end.
      cancel.
    }
    unfold store_solution.
    Exists L.
    sep_apply Haddr.
    sep_apply (store_array_missing_i_merge_to_array _ (store_type_addr s)
      &( "res") n 100 tp L).
    2: auto.
    assert (
      (&( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
       &( t1 # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
      |-- store_type t1 tr1_verify) as Htype. {
      subst.
      simpl store_type.
      repeat (split_pure_spatial || split_pures).
      all: try cancel.
      all: dump_pre_spatial; int_auto.
    }
    sep_apply Htype.
    assert (L = @replace_Znth addr n tp L) as Hreplace. {
      subst.
      match goal with
      | Hz : ?v = Znth n L 100 |- _ => rewrite Hz
      | Hz : Znth n L 100 = ?v |- _ => rewrite <- Hz
      end.
      rewrite replace_Znth_Znth.
      tauto.
    }
    rewrite Hreplace at 2.
    cancel.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_4 : atype_unify_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_which_implies_wit_4_split_goal_spatial.
  - Goal_apply proof_of_atype_unify_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_atype_unify_which_implies_wit_4_split_goal_2.
Qed.

Lemma not_var_helper: forall t1 tr1 t1_t,
  t1_t <> 3 ->
  &( t1 # "atype" ->ₛ "t") # Int |-> t1_t **
  store_type_aux t1 t1_t tr1
  |-- “ not_var tr1 ”.
Proof.
  intros.
  destruct tr1.
  + simpl not_var.
    simpl store_type_aux.
    Intros_p Htag.
    exfalso; lia.
  + dump_pre_spatial.
    simpl not_var; exact I.
  + dump_pre_spatial.
    simpl not_var; exact I.
  + dump_pre_spatial.
    simpl not_var; exact I.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_5_split_goal_1 :
  atype_unify_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply not_var_helper; auto.
  Intros_p Hnot.
  dump_pre_spatial.
  eapply repr_rel_node_not_var.
  exact Hnot.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_5_split_goal_spatial :
  atype_unify_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply from_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify_which_implies_wit_5 : atype_unify_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_which_implies_wit_5_split_goal_spatial.
  - Goal_apply proof_of_atype_unify_which_implies_wit_5_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_return_wit_5_split_goal_spatial :
  atype_unify1_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify1_return_wit_5 : atype_unify1_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify1_return_wit_6_split_goal_spatial :
  atype_unify1_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify1_return_wit_6 : atype_unify1_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_return_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_1 : atype_unify1_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply to_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_2 : atype_unify1_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct tr2.
  + simpl store_type_aux.
    Exists n.
    Intros_p Htag.
    Intros_p Hlo.
    Intros_p Hhi.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; auto.
  + unfold store_type_aux.
    Intros_p Htag.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
Qed.


Lemma proof_of_atype_unify1_which_implies_wit_3 : atype_unify1_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  2: {
    unfold store_option_type.
    Intros_p Hnull.
    exfalso.
    unfold NULL in Hnull.
    lia.
  }
  Exists t.
  unfold solution_at.
  split_pure_spatial.
  - unfold store_solution.
    Exists L.
    rename s_pre into s.
    assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
      (store_option_type tp (Some t)) |-- (store_type_addr s) &( "res") n tp) as Haddr. {
      unfold store_type_addr.
      match goal with
      | Hsn : Some t = s n |- _ => rewrite <- Hsn
      end.
      cancel.
    }
    sep_apply Haddr.
    cancel (&( t2 # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n).
    rewrite (store_array_missing_i_merge_to_array _  (store_type_addr s) &( "res") n 100 tp L).
    2: auto.
    assert (L = @replace_Znth addr n tp L) as Hreplace. {
      subst.
      rewrite replace_Znth_Znth.
      tauto.
    }
    rewrite Hreplace at 2.
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_4_split_goal_1 :
  atype_unify1_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  - unfold store_option_type.
    Intros_p Hnonnull.
    exfalso.
    unfold NULL in Hnonnull.
    lia.
  - dump_pre_spatial.
    rewrite PreH9.
    eapply repr_rel_node_var.
    eapply repr_rel_var; eauto.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_4_split_goal_2 :
  atype_unify1_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  destruct tr_opt.
  - unfold store_option_type.
    Intros_p Hnonnull.
    exfalso.
    unfold NULL in Hnonnull.
    lia.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_4_split_goal_spatial :
  atype_unify1_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_solution_aux.
  Intros L.
  rename s_pre into s.
  destruct tr_opt.
  - unfold store_option_type.
    Intros_p Hnonnull.
    exfalso.
    unfold NULL in Hnonnull.
    lia.
  - assert ((&( "res") + n * sizeof ( PTR )) # Ptr |-> tp **
      store_option_type tp None |-- (store_type_addr s) &( "res") n tp) as Haddr. {
      unfold store_type_addr.
      match goal with
      | Hsn : None = s n |- _ => rewrite <- Hsn
      end.
      cancel.
    }
    unfold store_solution.
    Exists L.
    sep_apply Haddr.
    sep_apply (store_array_missing_i_merge_to_array _ (store_type_addr s)
      &( "res") n 100 tp L).
    2: auto.
    assert (
      (&( t2 # "atype" ->ₛ "t") # Int |-> t2_t **
       &( t2 # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
      |-- store_type t2 tr2) as Htype. {
      subst.
      simpl store_type.
      repeat (split_pure_spatial || split_pures).
      all: try cancel.
      all: dump_pre_spatial; int_auto.
    }
    sep_apply Htype.
    assert (L = @replace_Znth addr n tp L) as Hreplace. {
      subst.
      match goal with
      | Hz : ?v = Znth n L 100 |- _ => rewrite Hz
      | Hz : Znth n L 100 = ?v |- _ => rewrite <- Hz
      end.
      rewrite replace_Znth_Znth.
      tauto.
    }
    rewrite Hreplace at 2.
    cancel.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_4 : atype_unify1_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_which_implies_wit_4_split_goal_spatial.
  - Goal_apply proof_of_atype_unify1_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_atype_unify1_which_implies_wit_4_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_5_split_goal_1 :
  atype_unify1_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply not_var_helper; auto.
  Intros_p Hnot.
  dump_pre_spatial.
  eapply repr_rel_node_not_var.
  exact Hnot.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_5_split_goal_spatial :
  atype_unify1_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply from_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify1_which_implies_wit_5 : atype_unify1_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_which_implies_wit_5_split_goal_spatial.
  - Goal_apply proof_of_atype_unify1_which_implies_wit_5_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_13_split_goal_spatial :
  atype_unify2_return_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify2_return_wit_13 : atype_unify2_return_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_13_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_split_goal_1 :
  atype_unify2_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  dump_pre_spatial.
  apply (unify_rel_left_var s_pre tr1_prev n tr2_prev tr2);
  tauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_split_goal_spatial :
  atype_unify2_return_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify2_return_wit_12 : atype_unify2_return_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_12_split_goal_spatial.
  - Goal_apply proof_of_atype_unify2_return_wit_12_split_goal_1.
Qed.


Lemma proof_of_atype_unify2_return_wit_11_split_goal_spatial :
  atype_unify2_return_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify2_return_wit_11 : atype_unify2_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_11_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_split_goal_1 :
  atype_unify2_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  dump_pre_spatial.
  eapply unify_rel_right_var; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_split_goal_spatial :
  atype_unify2_return_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_atype_unify2_return_wit_10 : atype_unify2_return_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_10_split_goal_spatial.
  - Goal_apply proof_of_atype_unify2_return_wit_10_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_9_split_goal_spatial :
  atype_unify2_return_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply from_aux.
  sep_apply from_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_9 : atype_unify2_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_9_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_8_split_goal_spatial :
  atype_unify2_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl store_type.
  Exists t1_from t1_to.
  Exists t2_from t2_to.
  cancel.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_8 : atype_unify2_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_8_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_split_goal_1 :
  atype_unify2_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  eapply unify_rel_arrow.
  - rewrite <- PreH10. exact PreH17.
  - rewrite <- PreH11. exact PreH18.
  - exact PreH9.
  - exact PreH6.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_split_goal_spatial :
  atype_unify2_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl store_type.
  Exists t1_from t1_to.
  Exists t2_from t2_to.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_6 : atype_unify2_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_atype_unify2_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_7_split_goal_spatial :
  atype_unify2_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl store_type.
  Exists t1_from t1_to.
  Exists t2_from t2_to.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_7 : atype_unify2_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_7_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_5_split_goal_spatial :
  atype_unify2_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl store_type.
  Exists t1_tfn t1_rand.
  Exists t2_tfn t2_rand.
  cancel.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_5 : atype_unify2_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_3_split_goal_1 :
  atype_unify2_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  eapply unify_rel_apply.
  - rewrite <- PreH10. exact PreH18.
  - rewrite <- PreH11. exact PreH19.
  - exact PreH9.
  - exact PreH6.
Qed.

Lemma proof_of_atype_unify2_return_wit_3_split_goal_spatial :
  atype_unify2_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl store_type.
  Exists t1_tfn t1_rand.
  Exists t2_tfn t2_rand.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_3 : atype_unify2_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_atype_unify2_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_4_split_goal_spatial :
  atype_unify2_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl store_type.
  Exists t1_tfn t1_rand.
  Exists t2_tfn t2_rand.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_4 : atype_unify2_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_return_wit_2_split_goal_1 :
  atype_unify2_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  dump_pre_spatial.
  eapply unify_rel_atom; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_2_split_goal_spatial :
  atype_unify2_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_2 : atype_unify2_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_atype_unify2_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_1_split_goal_spatial :
  atype_unify2_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_type.
  cancel.
  cancel.
Qed.

Lemma proof_of_atype_unify2_return_wit_1 : atype_unify2_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_1 : atype_unify2_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply to_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_2 : atype_unify2_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct tr1.
  + simpl store_type_aux.
    Exists n.
    Intros_p Htag.
    Intros_p Hlo.
    Intros_p Hhi.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; auto.
  + unfold store_type_aux.
    Intros_p Htag.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_3 : atype_unify2_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply to_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_4 : atype_unify2_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  destruct tr2.
  + simpl store_type_aux.
    Exists n.
    Intros_p Htag.
    Intros_p Hlo.
    Intros_p Hhi.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; auto.
  + unfold store_type_aux.
    Intros_p Htag.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
  + unfold store_type_aux.
    Intros p1 p2.
    exfalso; lia.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_5_split_goal_spatial :
  atype_unify2_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply from_aux.
  cancel.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_5 : atype_unify2_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_which_implies_wit_5_split_goal_spatial.
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
  destruct tr1; simpl store_type_aux.
  + Intros_p Htag.
    exfalso; lia.
  + Intros_p Htag.
    exfalso; lia.
  + Intros p1 p2.
    exfalso; lia.
  + Intros p1 p2.
    Exists p2 tr1_2 p1 tr1_1.
    split_pure_spatial.
    - cancel.
      cancel.
      cancel.
    - repeat split_pures; dump_pre_spatial; auto.
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
  destruct tr1; simpl store_type_aux.
  + Intros_p Htag.
    exfalso; lia.
  + Intros_p Htag.
    exfalso; lia.
  + Intros p1 p2.
    Exists p1 tr1_1 p2 tr1_2.
    split_pure_spatial.
    - cancel.
      cancel.
      cancel.
    - repeat split_pures; dump_pre_spatial; auto.
  + Intros p1 p2.
    exfalso; lia.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_6 : atype_unify2_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  sep_apply helper_1.
  Intros t1_to tr1_to t1_from tr1_from.
  sep_apply helper_1.
  Intros t2_to tr2_to t2_from tr2_from.
  Exists tr2_to t2_to tr2_from t2_from.
  Exists tr1_to t1_to tr1_from t1_from.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_7 : atype_unify2_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  sep_apply helper_2.
  Intros t1_tfn tr1_tfn t1_rand tr1_rand.
  sep_apply helper_2.
  Intros t2_tfn tr2_tfn t2_rand tr2_rand.
  Exists tr2_rand t2_rand tr2_tfn t2_tfn.
  Exists tr1_rand t1_rand tr1_tfn t1_tfn.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; auto.
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
    Intros_p Htag.
    exfalso; lia.
  + simpl store_type_aux.
    Exists n.
    Intros_p Htag.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial; auto.
  + simpl store_type_aux.
    Intros p1 p2.
    exfalso; lia.
  + simpl store_type_aux.
    Intros p1 p2.
    exfalso; lia.
Qed.

Lemma proof_of_atype_unify2_which_implies_wit_8 : atype_unify2_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  sep_apply last; auto.
  Intros n.
  sep_apply last; auto.
  Intros m.
  Exists m n.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; auto.
Qed.


Lemma proof_of_atype_unify_derive_final_by_verify : 
  atype_unify_derive_final_by_verify.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename s_pre_final into s_cpre.
  unfold store_compressed_solution at 1.
  Intros s_pre.
  Exists s_pre tr1_final tr2_final.
  cancel (store_solution &( "res") s_pre).
  cancel (store_type t1_pre tr1_final).
  cancel (store_type t2_pre tr2_final).
  rewrite <- derivable1_wand_sepcon_adjoint.
  Split.
  - Intros s_post retval.
    pose proof (unify_soundness tr1_final tr2_final s_pre s_post s_cpre H H1 H0 H3).
    destruct H4 as [s_cpost ?].
    Left.
    Exists s_cpost retval.
    unfold store_compressed_solution.
    Exists s_post.
    split_pure_spatial.
    + repeat cancel.
    + repeat split_pures; dump_pre_spatial; tauto.
  - Intros s_post retval.
    Right. 
    Exists s_post retval.
    split_pure_spatial.
    + repeat cancel.
    + dump_pre_spatial; auto.
Qed.
