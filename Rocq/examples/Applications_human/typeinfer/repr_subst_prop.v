Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list.
Local Open Scope Z_scope.
Require Import Lia.
Require Import Coq.Logic.Classical_Prop.
From SimpleC.EE.Applications_human.typeinfer Require Import type_infer_lib.

Lemma repr_rel_id_rhs_var: forall s n m,
  repr_rel_id s n (TVar m) -> s m = None.
Proof.
  intros.
  remember (TVar m) as vm.
  induction H.
  + inversion Heqvm.
    subst m.
    assumption.
  + subst t.
    inversion H0.
  + subst t.
    apply IHrepr_rel_id.
    reflexivity.
Qed.

Lemma repr_rel_node_rhs_var: forall s t n,
  repr_rel_node s t (TVar n) -> s n = None.
Proof.
  intros.
  inversion H.
  + subst t.
    apply repr_rel_id_rhs_var in H0.
    assumption.
  + contradiction.
Qed.

Lemma repr_rel_node_rhs: forall s t t',
  repr_rel_node s t t' -> (not_var t' \/
      (exists v, t' = TVar v /\ s v = None)).
Proof.
  intros.
  destruct t'.
  2,3,4: left; simpl not_var; tauto.
  right.
  exists n.
  split; auto.
  inversion H; subst; try contradiction.
  clear H.
  apply repr_rel_id_rhs_var in H0.
  assumption.
Qed.


Lemma subst_same_no_var_some: forall (s: sol) (t: TypeTree),
  (forall n, occur n t -> s n = None) ->
  type_subst t s = t.
Proof.
  intros.
  induction t.
  3,4:
    simpl;
    f_equal; [ rewrite IHt1 | rewrite IHt2 ];
    try reflexivity;
    clear IHt1 IHt2;
    intros;
    specialize (H n);
    simpl in H;
    rewrite H;
    try tauto.
  + specialize (H n).
    simpl in H.
    assert (n = n) as H1.
    reflexivity.
    specialize (H H1).
    simpl.
    rewrite H.
    reflexivity.
  + simpl.
    reflexivity.
Qed.


Lemma occur_sol_right_then_none: forall sc n t,
  sol_compressed sc ->
  sc n = Some(t) ->
  (forall m, occur m t -> sc m = None).
Proof.
  intros.
  specialize (H n m).
  rewrite H0 in H.
  destruct (sc m) eqn: Hm.
  + contradiction.
  + reflexivity.
Qed.


Lemma subst_same_twice: forall sc t1 t2,
  sol_compressed sc ->
  type_subst t1 sc = t2 ->
  type_subst t2 sc = t2.
Proof.
  intros.
  revert t2 H0.
  induction t1; intros.
  + simpl in H0.
    destruct (sc n) eqn:Hn.
    2: {
      subst t2.
      simpl.
      rewrite Hn.
      reflexivity.
    }
    subst t2.
    specialize (occur_sol_right_then_none _ _ _ H Hn) as Hc.
    apply (subst_same_no_var_some _ _ Hc).
  + simpl in H0.
    subst t2.
    simpl.
    reflexivity.
  + destruct t2 eqn:Ht2;
    inversion H0.
    specialize (IHt1_1 _ H2).
    specialize (IHt1_2 _ H3).
    rewrite H2.
    rewrite H3.
    simpl.
    f_equal; f_equal; assumption.
  + destruct t2 eqn:Ht2;
    inversion H0.
    specialize (IHt1_1 _ H2).
    specialize (IHt1_2 _ H3).
    rewrite H2.
    rewrite H3.
    simpl.
    f_equal; f_equal; assumption.
Qed.

Lemma subst_same_sol_right: forall s n t,
  sol_compressed s ->
  s n = Some(t) ->
  type_subst t s = t.
Proof.
  intros.
  apply (subst_same_twice _ (TVar n) t H).
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Lemma none_occur_after_subst: forall (s: sol) (t: TypeTree) (n: TypeVarID),
  sol_compressed s ->
  occur n (type_subst t s) ->
  s n = None.
Proof.
  intros s t n C_s.
  revert n.
  induction t; intros n1 Occ.
  + simpl type_subst in Occ.
    destruct (s n) eqn:Hsn0.
    - specialize (C_s n n1).
      rewrite Hsn0 in C_s.
      destruct (s n1) eqn:Hsn1.
      contradiction.
      reflexivity.
    - simpl occur in Occ.
      subst n1.
      assumption.
  + simpl type_subst in Occ.
    simpl occur in Occ.
    contradiction.
  + specialize (IHt1 n1).
    specialize (IHt2 n1).
    inversion Occ.
    apply (IHt1 H).
    apply (IHt2 H).
  + specialize (IHt1 n1).
    specialize (IHt2 n1).
    inversion Occ.
    apply (IHt1 H).
    apply (IHt2 H).
Qed.


Lemma some_not_occur_after_subst: forall s t n,
  sol_compressed s ->
  s n <> None ->
  ~occur n (type_subst t s).
Proof.
  intros.
  specialize (none_occur_after_subst s t n H) as H1.
  intros contra.
  apply H1 in contra.
  contradiction.
Qed.

Lemma none_keep_occur_after_subst : forall s sc n t,
  sol_compress_to s sc ->
  s n = None ->
  occur n t ->
  occur n (type_subst t sc).
Proof.
  intros.
  unfold sol_compress_to in H. 
  destruct H.
  induction t ; simpl in * ; intros; subst ; auto.
    - pose proof (H2 n0). rewrite H0 in H1. rewrite H1.
      reflexivity.
    - tauto.
    - tauto.
Qed.


Lemma none_occur_after_subst_var: forall s t tn n m,
  sol_compressed s ->
  type_subst t s = t ->
  s n = None ->
  occur m (type_subst_var t n (type_subst tn s)) ->
  s m = None.
Proof.
  intros.
  induction t; intros.
  + simpl in H2.
    destruct (Z.eq_dec n n0) as [ Hnn0 | Hnn0 ].
    - subst n0.
      apply (none_occur_after_subst s tn m H H2).
    - simpl in H2.
      simpl in H0.
      destruct (s n0) eqn:Hsn0.
      * subst t.
        specialize (H n0 n0).
        rewrite Hsn0 in H.
        simpl in H.
        contradiction.
      * subst n0.
        assumption.
  + simpl in H2.
    contradiction.
  + simpl in H0.
    inversion H0.
    specialize (IHt1 H4).
    specialize (IHt2 H5).
    simpl in H2.
    destruct H2.
    - apply (IHt1 H2).
    - apply (IHt2 H2).
  + simpl in H0.
    inversion H0.
    specialize (IHt1 H4).
    specialize (IHt2 H5).
    simpl in H2.
    destruct H2.
    - apply (IHt1 H2).
    - apply (IHt2 H2).
Qed.


Lemma some_not_occur_after_subst_var: forall s t tn n m,
  sol_compressed s ->
  type_subst t s = t ->
  s n = None ->
  s m <> None ->
  ~occur m (type_subst_var t n (type_subst tn s)).
Proof.
  intros.
  specialize (none_occur_after_subst_var s t tn n m H H0 H1) as HH.
  intros contra.
  specialize (HH contra).
  contradiction.
Qed.

Lemma self_not_occur_after_subst_var: forall s t tn n,
  sol_compressed s ->
  type_subst t s = t ->
  s n = None ->
  ~occur n (type_subst tn s) ->
  ~occur n (type_subst_var t n (type_subst tn s)).
Proof.
  intros.
  induction t.
  + simpl.
    destruct (Z.eq_dec n n0).
    - subst n0.
      assumption.
    - simpl.
      assumption.
  + simpl.
    tauto.
  + inversion H0.
    simpl.
    specialize (IHt1 H4).
    specialize (IHt2 H5).
    rewrite H4, H5.
    apply and_not_or.
    split; tauto.
  + inversion H0.
    simpl.
    specialize (IHt1 H4).
    specialize (IHt2 H5).
    rewrite H4, H5.
    apply and_not_or.
    split; tauto.
Qed.

Lemma simpl_repr_rel_node_var: forall s n t,
  repr_rel_node s (TVar n) t ->
  repr_rel_id s n t.
Proof.
  intros.
  inversion H.
  + assumption.
  + contradiction.
Qed.

Ltac unfold_repr_rel_node H :=
  match type of H with
  | repr_rel_node ?s ?t ?ts =>
      let H' := fresh "H" in
      assert (H': ts = t) by (inversion H; reflexivity)
  end.

Lemma repr_rel_subst_same: forall s sc t1 t2,
  sol_compress_to s sc ->
  repr_rel_node s t1 t2 ->
  type_subst t1 sc = type_subst t2 sc.
Proof.
  intros.
  destruct H0.
  2: reflexivity.
  simpl.
  induction H0.
  + reflexivity.
  + specialize ((proj2 H) n) as Hscn.
    rewrite H0 in Hscn.
    rewrite Hscn.
    reflexivity.
  + simpl type_subst in IHrepr_rel_id at 1.
    specialize ((proj2 H) n) as Hscn.
    rewrite H0 in Hscn.
    simpl in Hscn.
    destruct (sc m) eqn:Hscm;
      rewrite Hscn;
      assumption.
Qed.



Lemma repr_rel_id_to_subst: forall s sc n t,
  sol_compress_to s sc ->
  repr_rel_id s n t ->
  ((s n <> None /\ sc n = Some(type_subst t sc)) \/
  (s n = None /\ sc n = None /\ t = TVar n)).
Proof.
  intros.
  specialize (repr_rel_subst_same s sc (TVar n) t H) as H1.
  destruct H1.
  1: apply (repr_rel_node_var s n t H0).
  unfold type_subst.
  destruct (sc n) eqn:Hscn.
  1: {
    left.
    split; [ | reflexivity ].
    specialize (proj2 H n) as Occ.
    destruct (s n) eqn:Hsn.
    discriminate.
    rewrite Hscn in Occ.
    inversion Occ.
  }
  right.
  specialize (proj2 H n) as Occ.
  destruct (s n) eqn:Hsn.
  rewrite Hscn in Occ.
  inversion Occ.
  intuition; try reflexivity.
  inversion H0; [ reflexivity | | ];
  rewrite Hsn in H1;
  inversion H1.
Qed.

Lemma subst_twice_refine_eq: forall sc scf t,
  sol_compressed sc ->
  sol_compressed scf ->
  sol_refine sc scf ->
  type_subst (type_subst t sc) scf = type_subst t scf.
Proof.
  intros.
  red in H1.
  symmetry.
  eapply H1.
Qed.

Lemma unfold_subst_var_equal: forall sc n1 n2,
  sol_compressed sc ->
  type_subst (TVar n1) sc = type_subst (TVar n2) sc ->
  ((sc n1 = sc n2 /\ sc n1 <> None) \/
  (sc n1 = Some(TVar n2) /\ sc n2 = None) \/
  (sc n1 = None /\ sc n2 = Some(TVar n1)) \/
  (sc n1 = None /\ n1 = n2)).
Proof.
  intros.
  inversion H0.
  destruct (sc n1) eqn:Hn1, (sc n2) eqn:Hn2.
  + left.
    rewrite H2.
    split; [ tauto | ].
    discriminate.
  + right. left.
    subst t.
    split; reflexivity.
  + right. right. left.
    subst t.
    split; reflexivity.
  + repeat right.
    split; [ reflexivity | ].
    inversion H2.
    reflexivity.
Qed.

Lemma subst_keep_same_update: forall s n t tn,
  sol_compressed s ->
  ~occur n tn ->
  type_subst tn s = tn ->
  ~occur n t ->
  type_subst t s = t ->
  (* Hint: sp = sol_c_update s n *)
  type_subst t (sol_c_update s n tn) = t.
Proof.
  intros s n t tn C_s Occ_tn Htn Occ_t Ht.
  remember (sol_c_update s n tn) as sp.
  induction t.
  3, 4:
    simpl in Occ_t;
    apply not_or_and in Occ_t;
    inversion Ht as [ [ Subst_t1 Subst_t2 ] ];
    specialize (IHt1 (proj1 Occ_t) Subst_t1);
    specialize (IHt2 (proj2 Occ_t) Subst_t2);
    simpl;
    f_equal;
    try rewrite Subst_t1, IHt1;
    try rewrite Subst_t2, IHt2;
    try reflexivity.
  2: {
    simpl.
    reflexivity.
  }
  inversion Ht.
  destruct (s n0) eqn:Hsn0.
  1: {
   specialize (C_s n0 n0).
    rewrite Hsn0 in C_s.
    subst t.
    simpl in C_s.
    contradiction.
  }
  clear H0.
  simpl.
  destruct (sp n0) eqn:Hspn0; [ | reflexivity ].
  simpl in Occ_t.
  subst sp.
  unfold sol_c_update in Hspn0.
  destruct (Z.eq_dec n n0) as [ Hnn0 | _ ]; [ contradiction | ].
  rewrite Hsn0 in Hspn0.
  inversion Hspn0.
Qed.

Lemma subst_not_occur: forall sc scp n tn t
  (Hscp: scp = sol_c_update sc n (type_subst tn sc))
  (C_sc: sol_compressed sc),
  (forall m, occur m t -> sc m = None) ->
  ~occur n t ->
  type_subst t scp = t.
Proof.
  intros.
  induction t.
  3, 4:
    simpl in H0; apply not_or_and in H0;
    destruct H0 as [ Occ1 Occ2 ];
    simpl; f_equal; [ apply IHt1 | apply IHt2 ]; auto;
    intros; apply (H m); simpl; auto.
  2: simpl; reflexivity.
  specialize (H n0).
  simpl in H, H0.
  unfold type_subst; rewrite Hscp; unfold sol_c_update.
  destruct (Z.eq_dec n n0) as [ Hnn0 | _ ]; [ congruence | ].
  assert (sc n0 = None) as Hscn0 by (apply H; reflexivity).
  rewrite Hscn0.
  reflexivity.
Qed.


Lemma subst_not_occur_same: forall sc scp n tn,
  scp = sol_c_update sc n (type_subst tn sc) ->
  sol_compressed sc ->
  ~occur n (type_subst tn sc) ->
  sc n = None ->
  forall t,
  ~occur n (type_subst t sc) ->
  type_subst (type_subst t sc) scp = type_subst t sc.
Proof.
  intros.
  induction t.
  3, 4:
    simpl in H3; apply not_or_and in H3; simpl; intuition;
    f_equal; auto.
  2: simpl; reflexivity.
  rename n0 into n1.
  assert (n <> n1) as Hnn1. {
    intros contra; subst n1.
    simpl in H3; rewrite H2 in H3.
    congruence.
  }
  simpl; destruct (sc n1) eqn:Hscn1.
  2: {
    unfold type_subst.
    rewrite H. unfold sol_c_update.
    rewrite Hscn1.
    destruct (Z.eq_dec n n1); [ contradiction | reflexivity ].
  }
  eapply (subst_not_occur _ _ _ _ _ H); auto.
  + intros.
    specialize (H0 n1 m); rewrite Hscn1 in H0.
    destruct (sc m); [ congruence | reflexivity ].
  + unfold type_subst in H3.
    rewrite Hscn1 in H3.
    assumption.
Qed.


Lemma call_impl_subst: forall s n t,
	s n = Some(t) ->
	type_subst (TVar n) s = t.
Proof.
	intros.
	unfold type_subst.
	rewrite H.
	reflexivity.
Qed.


Lemma subst_impl_call: forall s n t,
	t <> TVar n ->
	type_subst (TVar n) s = t ->
	s n = Some(t).
Proof.
	intros.
	unfold type_subst in H0.
	destruct (s n) eqn: Hsn.
	+ subst t0; reflexivity.
	+ symmetry in H0.
	  contradiction.
Qed.

