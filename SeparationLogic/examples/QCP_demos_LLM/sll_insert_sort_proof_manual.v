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
Require Import SimpleC.EE.QCP_demos_LLM.sll_insert_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.sll_insert_sort_lib.
Local Open Scope sac.

Lemma upperbound_insert_app:
  forall x l1 l2,
    strict_upperbound x l1 ->
    insert x (l1 ++ l2) = l1 ++ insert x l2.
Proof.
  intros x l1 l2 Hupper.
  revert l2 Hupper.
  induction l1; intros l2 Hupper.
  - reflexivity.
  - simpl in Hupper.
    destruct Hupper.
    simpl.
    destruct (x >? a) eqn:Hgt.
    + f_equal.
      apply IHl1.
      exact H0.
    + lia.
Qed.

Lemma proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Proof.
  pre_process.
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
  pre_process.
  Exists y.
  Exists (l1_2 ++ x :: nil)%list.
  Exists l0.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 p2 p2_v_2 x); [ | assumption ].
    sep_apply (sllbseg_sllbseg (&( "res" )) p2 (&((p2_v_2) # "list" ->ₛ "next")) l1_2 (x :: nil)%list).
    cancel.
  - split_pures; try (dump_pre_spatial; apply upperbound_app; try assumption; lia).
    dump_pre_spatial ; auto.
    dump_pre_spatial.
    rewrite PreH5.
    rewrite PreH2.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_insertion_entail_wit_3_1 : insertion_entail_wit_3_1.
Proof.
  pre_process.
  subst p2_v.
  sep_apply (sll_zero 0 l2); [ | reflexivity ].
  Intros_p Hl2.
  Left.
  Exists l1_3.
  split_pure_spatial.
  - cancel ((&((node_pre) # "list" ->ₛ "data")) # Int |-> a).
    cancel (sllbseg ( &( "res" ) ) p2 l1_3).
    cancel ((p2) # Ptr |-> 0).
    cancel ((&((node_pre) # "list" ->ₛ "next")) # Ptr |->_).
  - split_pures.
    + dump_pre_spatial.
      exact PreH2.
    + dump_pre_spatial.
      rewrite Hl2 in PreH3.
      exact PreH3.
    + dump_pre_spatial.
      exact PreH4.
Qed.

Lemma proof_of_insertion_entail_wit_4_1 : insertion_entail_wit_4_1.
Proof.
  pre_process.
  Left.
  sep_apply (sllbseg_2_sllseg (&( "res" )) p2 node_pre l1_3).
  Intros resv_2.
  Exists resv_2.
  Exists l1_3.
  split_pure_spatial.
  - cancel ((( &( "res" ) )) # Ptr |-> resv_2).
    cancel (sllseg resv_2 node_pre l1_3).
    cancel ((&((node_pre) # "list" ->ₛ "data")) # Int |-> a).
    cancel ((&((node_pre) # "list" ->ₛ "next")) # Ptr |-> 0).
  - split_pures.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      exact PreH2.
    + dump_pre_spatial.
      exact PreH3.
Qed.

Lemma proof_of_insertion_entail_wit_4_2 : insertion_entail_wit_4_2.
Proof.
  pre_process.
  Right.
  sep_apply (sllbseg_2_sllseg (&( "res" )) p2 node_pre l1_3).
  Intros resv.
  Exists unext_2.
  Exists resv.
  Exists l1_3.
  Exists l0_2.
  Exists x_2.
  Exists u_2.
  split_pure_spatial.
  - cancel ((( &( "res" ) )) # Ptr |-> resv).
    cancel (sllseg resv node_pre l1_3).
    cancel ((&((node_pre) # "list" ->ₛ "data")) # Int |-> a).
    cancel ((&((node_pre) # "list" ->ₛ "next")) # Ptr |-> u_2).
    cancel ((&((u_2) # "list" ->ₛ "data")) # Int |-> x_2).
    cancel ((&((u_2) # "list" ->ₛ "next")) # Ptr |-> unext_2).
    cancel (sll unext_2 l0_2).
  - split_pures.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      exact PreH2.
    + dump_pre_spatial.
      exact PreH3.
    + dump_pre_spatial.
      exact PreH4.
    + dump_pre_spatial.
      exact PreH5.
Qed.

Lemma proof_of_insertion_return_wit_1 : insertion_return_wit_1.
Proof.
  pre_process.
  Exists ((l1 ++ a :: nil)%list).
  split_pure_spatial.
  - sep_apply (sllseg_len1 node_pre a 0); [ | tauto ].
    sep_apply (sllseg_sll resv node_pre l1 (a :: nil)%list).
    cancel (sll resv (l1 ++ a :: nil)%list).
  - dump_pre_spatial.
    rewrite PreH2.
    rewrite app_nil_r.
    symmetry.
    apply upperbound_insert_nil.
    exact PreH3.
Qed.

Lemma proof_of_insertion_return_wit_2 : insertion_return_wit_2.
Proof.
  pre_process.
  Exists (((l1 ++ a :: nil)%list ++ x :: l0_2)%list).
  split_pure_spatial.
  - sep_apply (sllseg_len1 node_pre a u); [ | tauto ].
    sep_apply (sllseg_sllseg resv node_pre u l1 (a :: nil)%list).
    sep_apply_r_atomic (sllseg_sll resv u (l1 ++ a :: nil)%list (x :: l0_2)).
    simpl sll.
    Exists unext.
    split_pure_spatial.
    + cancel (sllseg resv u (l1 ++ a :: nil)%list).
      cancel ((&((u) # "list" ->ₛ "data")) # Int |-> x).
      cancel ((&((u) # "list" ->ₛ "next")) # Ptr |-> unext).
      cancel (sll unext l0_2).
    + dump_pre_spatial.
      exact PreH2.
  - dump_pre_spatial.
    rewrite PreH4.
    assert (a <= x) by lia.
    rewrite (upperbound_insert_cons a l1 l0_2 x PreH5 H).
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Proof.
  pre_process.
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
  pre_process.
  Exists l0_4.
  Exists (l1_2 ++ x :: nil)%list.
  Exists l0_3.
  split_pure_spatial.
  - sep_apply store_ptr_undef_store_ptr.
    cancel (sll retval l0_4).
    cancel (sll y l0_3).
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
  pre_process.
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
