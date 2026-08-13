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
From SimpleC.EE.QCP_demos_human Require Import sll_insert_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import sll_insert_sort_lib.
Local Open Scope sac.

Lemma proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil.
  Exists l.
  split_pure_spatial.
  - cancel (&((node_pre) # "list" ->ₛ "data") # Int |-> a).
    cancel (sll p_pre l).
    cancel (&((node_pre) # "list" ->ₛ "next") # Ptr |->_).
    simpl sllbseg.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - split_pures; try (dump_pre_spatial; auto).
Qed.

Lemma proof_of_insertion_entail_wit_2 : insertion_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  inversion PreH1; subst.
  Exists p2_v_next.
  Exists (l1_2 ++ p2_v_data :: nil)%list.
  Exists l3.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 p2 p2_v_2 p2_v_data); [ | assumption ].
    sep_apply (sllbseg_sllbseg (&( "res" )) p2 (&((p2_v_2) # "list" ->ₛ "next")) l1_2 (p2_v_data :: nil)%list).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite <- app_assoc.
      reflexivity.
    + dump_pre_spatial.
      apply upperbound_app; [exact PreH6 | exact PreH2].
    + dump_pre_spatial.
      exact PreH7.
Qed.

Lemma proof_of_insertion_return_wit_1 : insertion_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p2_v.
  sep_apply (sll_zero 0 l2); [ | reflexivity ].
  Intros_p Hl2.
  Exists ((l1 ++ a :: nil)%list).
  split_pure_spatial.
  - sep_apply (sllseg_len1 node_pre a 0); [ | tauto ].
    sep_apply (sllseg_sll res node_pre l1 (a :: nil)%list).
    cancel.
  - dump_pre_spatial.
    rewrite Hl2 in PreH2.
    rewrite app_nil_r in PreH2.
    subst l.
    symmetry.
    apply upperbound_insert_nil.
    exact PreH3.
Qed.

Lemma proof_of_insertion_return_wit_2 : insertion_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (((l1 ++ a :: nil)%list ++ x :: l0_2)%list).
  split_pure_spatial.
  - sep_apply (sllseg_len1 node_pre a p2_v); [ | tauto ].
    sep_apply (sllseg_sllseg res node_pre p2_v l1 (a :: nil)%list).
    sep_apply_r_atomic (sllseg_sll res p2_v (l1 ++ a :: nil)%list (x :: l0_2)).
    simpl sll.
    Exists y.
    split_pure_spatial.
    + cancel (sllseg res p2_v (l1 ++ a :: nil)%list).
      cancel ((&((p2_v) # "list" ->ₛ "data")) # Int |-> x).
      cancel ((&((p2_v) # "list" ->ₛ "next")) # Ptr |-> y).
      cancel (sll y l0_2).
    + dump_pre_spatial.
      exact PreH3.
  - dump_pre_spatial.
    rewrite PreH4.
    rewrite PreH2.
    assert (a <= x) by lia.
    rewrite (upperbound_insert_cons a l1 l0_2 x PreH5 H).
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_insertion_which_implies_wit_2 : insertion_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  sep_apply sllbseg_2_sllseg.
  Intros y'. Exists y'.
  cancel.
Qed. 

Lemma proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil.
  Exists nil.
  Exists l.
  split_pure_spatial.
  - simpl sll.
    split_pure_spatial.
    + cancel (sll x_pre l).
    + dump_pre_spatial.
      reflexivity.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l0_3.
  Exists (l1_2 ++ p_data :: nil)%list.
  Exists l3.
  split_pure_spatial.
  - sep_apply store_ptr_undef_store_ptr.
    cancel (sll retval l0_3).
    cancel (sll p_next l3).
    cancel (((&( "q" ))) # Ptr |->_).
  - split_pures.
    + dump_pre_spatial.
      rewrite PreH4.
      rewrite PreH2.
      rewrite <- app_assoc.
      reflexivity.
    + dump_pre_spatial.
      rewrite PreH1.
      rewrite <- perm_insert.
      rewrite PreH5.
      reflexivity.
    + dump_pre_spatial.
      rewrite PreH1.
      apply increasing_insert.
      exact PreH6.
Qed.

Lemma proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  sep_apply (sll_zero 0 l2); [ | reflexivity ].
  Intros_p Hl2.
  Exists l0_2.
  split_pure_spatial.
  - rewrite Hl2 in PreH2.
    rewrite app_nil_r in PreH2.
    subst l.
    cancel (sll res l0_2).
  - split_pures.
    + dump_pre_spatial.
      rewrite Hl2 in PreH2.
      rewrite app_nil_r in PreH2.
      subst l.
      exact PreH3.
    + dump_pre_spatial.
      exact PreH4.
Qed.
