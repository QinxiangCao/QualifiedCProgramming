Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list.
Local Open Scope Z_scope.
Require Import Lia.
Require Import Coq.Logic.Classical_Prop.
From SimpleC.EE.Applications_human.typeinfer Require Import type_infer_lib.
From SimpleC.EE.Applications_human.typeinfer Require Import repr_subst_prop.
From SimpleC.EE.Applications_human.typeinfer Require Import sol_prop.

Lemma sol_update_keep_finite: forall s n t,
  sol_finite s ->
  sol_finite (sol_c_update s n t).
Proof.
  intros.
  unfold sol_finite in *.
  destruct H as [ l H ].
  exists (n :: l).
  intros.
  split.
  + intros.
    simpl in H0.
    destruct H0.
    - subst n0.
      unfold sol_c_update.
      destruct (Z.eq_dec n n) as [ _ | a ]; [ | contradiction ].
      discriminate.
    - specialize (H n0).
      destruct H as [ H _ ].
      specialize (H H0).
      unfold sol_c_update.
      destruct (Z.eq_dec n n0); [ discriminate | ].
      destruct (s n0); [ | contradiction ].
      discriminate.
  + intros.
    unfold sol_c_update in H0.
    destruct (Z.eq_dec n n0) as [ Hnn0 | Hnn0 ].
    - subst n0.
      simpl.
      tauto.
    - destruct (s n0) eqn:Hsn0; [ | contradiction ].
      simpl.
      right.
      specialize (H n0).
      destruct H as [ _ H ].
      apply H.
      rewrite Hsn0.
      discriminate.
Qed.


Lemma sol_refine_keep_valid_eq: forall sc scf t1 t2,
  sol_compressed sc ->
  sol_compressed scf ->
  sol_refine sc scf ->
  sol_valid_eq t1 t2 sc ->
  sol_valid_eq t1 t2 scf.
Proof.
  intros.
  unfold sol_valid_eq in *.
  specialize (H1 t1) as Hscft1.
  specialize (H1 t2) as Hscft2.
  rewrite Hscft1, Hscft2.
  f_equal; auto.
Qed.


Lemma simpl_repr_rel_id_to_TArrow: forall s sc n t1 t2,
  sol_compress_to s sc ->
  repr_rel_id s n (TArrow t1 t2) ->
  sc n = Some(TArrow (type_subst t1 sc) (type_subst t2 sc)).
Proof.
  intros.
  specialize (repr_rel_id_to_subst _ _ _ _ H H0) as H1.
  destruct H1 as [ [ Hsn Hscn ] | [ _ [ _ W ] ] ].
  + simpl type_subst in Hscn.
    assumption.
  + inversion W.
Qed.


Lemma refine_valid_part_to_full_TArrow:
  forall sc scf t1 t2 t11 t12 t21 t22
  (Rf: sol_refine sc scf)
  (St1: type_subst t1 sc = type_subst (TArrow t11 t12) sc)
  (St2: type_subst t2 sc = type_subst (TArrow t21 t22) sc)
  (ValidL: sol_valid_eq t11 t21 scf)
  (ValidR: sol_valid_eq t12 t22 scf),
  sol_valid_eq t1 t2 scf.
Proof.
  intros.
  red.
  red in ValidL, ValidR.
  simpl in *.
  specialize (Rf t1) as Ht1.
  specialize (Rf t2) as Ht2.
  rewrite St1 in Ht1.
  rewrite St2 in Ht2.
  simpl in *.
  rewrite Ht1, Ht2.
  f_equal.
  + rewrite <- (Rf t11), <- (Rf t21); auto.
  + rewrite <- (Rf t12), <- (Rf t22); auto.
Qed.
Lemma refine_valid_part_to_full_TApply:
  forall sc scf t1 t2 t11 t12 t21 t22
  (Rf: sol_refine sc scf)
  (St1: type_subst t1 sc = type_subst (TApply t11 t12) sc)
  (St2: type_subst t2 sc = type_subst (TApply t21 t22) sc)
  (ValidL: sol_valid_eq t11 t21 scf)
  (ValidR: sol_valid_eq t12 t22 scf),
  sol_valid_eq t1 t2 scf.
Proof.
  intros.
  red.
  red in ValidL, ValidR.
  simpl in *.
  specialize (Rf t1) as Ht1.
  specialize (Rf t2) as Ht2.
  rewrite St1 in Ht1.
  rewrite St2 in Ht2.
  simpl in *.
  rewrite Ht1, Ht2.
  f_equal.
  + rewrite <- (Rf t11), <- (Rf t21); auto.
  + rewrite <- (Rf t12), <- (Rf t22); auto.
Qed.


Lemma unify_induction_sol_tight_TArrow:
  forall (spre scpre sc1 sc2: sol),
  forall (t1 t11 t12 t2 t21 t22: TypeTree),
  forall (sf: sol),
  sol_compress_to spre scpre ->
  sol_compressed sc1 ->
  sol_compressed sc2 ->
  sol_compressed sf ->
  type_subst t1 scpre = type_subst (TArrow t11 t12) scpre ->
  type_subst t2 scpre = type_subst (TArrow t21 t22) scpre ->
  sol_correct_iter t11 t21 scpre sc1 ->
  sol_correct_iter t12 t22 sc1 sc2 ->
  sol_valid_eq t1 t2 sf ->
  sol_refine scpre sf ->
  sol_refine sc2 sf.
Proof.
  intros spre scpre sc1 sc2.
  intros t1 t11 t12 t2 t21 t22.
  intros sf.
  intros C_spre2scpre C_sc1 C_sc2 C_sf.
  intros St1 St2.
  intros CrtL CrtR Valid Rf.
  apply (f_equal (fun x => type_subst x sf)) in St1, St2.
  simpl in St1, St2.
  destruct C_spre2scpre as [ C_scpre C_spre2scpre ].
  repeat rewrite (subst_twice_refine_eq _ _ _ C_scpre C_sf Rf) in St1.
  repeat rewrite (subst_twice_refine_eq _ _ _ C_scpre C_sf Rf) in St2.
  unfold sol_valid_eq in Valid.
  rewrite St1, St2 in Valid.
  inversion Valid as [ [ ValidL ValidR ] ].
  apply (CrtR sf C_sf).
  split.
  1: red; assumption.
  specialize (CrtL sf C_sf).
  apply CrtL.
  split; [ assumption | tauto ].
Qed.
Lemma unify_induction_sol_tight_TApply:
  forall (spre scpre sc1 sc2: sol),
  forall (t1 t11 t12 t2 t21 t22: TypeTree),
  forall (sf: sol),
  sol_compress_to spre scpre ->
  sol_compressed sc1 ->
  sol_compressed sc2 ->
  sol_compressed sf ->
  type_subst t1 scpre = type_subst (TApply t11 t12) scpre ->
  type_subst t2 scpre = type_subst (TApply t21 t22) scpre ->
  sol_correct_iter t11 t21 scpre sc1 ->
  sol_correct_iter t12 t22 sc1 sc2 ->
  sol_valid_eq t1 t2 sf ->
  sol_refine scpre sf ->
  sol_refine sc2 sf.
Proof.
  intros spre scpre sc1 sc2.
  intros t1 t11 t12 t2 t21 t22.
  intros sf.
  intros C_spre2scpre C_sc1 C_sc2 C_sf.
  intros St1 St2.
  intros CrtL CrtR Valid Rf.
  apply (f_equal (fun x => type_subst x sf)) in St1, St2.
  simpl in St1, St2.
  destruct C_spre2scpre as [ C_scpre C_spre2scpre ].
  repeat rewrite (subst_twice_refine_eq _ _ _ C_scpre C_sf Rf) in St1.
  repeat rewrite (subst_twice_refine_eq _ _ _ C_scpre C_sf Rf) in St2.
  unfold sol_valid_eq in Valid.
  rewrite St1, St2 in Valid.
  inversion Valid as [ [ ValidL ValidR ] ].
  apply (CrtR sf C_sf).
  split.
  1: red; assumption.
  specialize (CrtL sf C_sf).
  apply CrtL.
  split; [ assumption | tauto ].
Qed.


Fixpoint occur_dec (n : TypeVarID) (t : TypeTree) : bool :=
  match t with
  | TVar n' => Z.eqb n n'
  | TAtom _ => false
  | TArrow t1 t2 => orb (occur_dec n t1) (occur_dec n t2)
  | TApply t1 t2 => orb (occur_dec n t1) (occur_dec n t2)
  end.

Lemma occur_dec_correct : forall n t , occur n t <-> occur_dec n t = true.
Proof.
  intros. induction t ; simpl ; split ; intros ; try lia.
  - destruct H ; [rewrite IHt1 in H | rewrite IHt2 in H ] ; rewrite H ; lia.
  - destruct (occur_dec n t1) ; destruct (occur_dec n t2) ; simpl in * ; auto ; tauto.
  - destruct H ; [rewrite IHt1 in H | rewrite IHt2 in H ] ; rewrite H ; lia.
  - destruct (occur_dec n t1) ; destruct (occur_dec n t2) ; simpl in * ; auto ; tauto.
Qed.  
    
Lemma none_not_occur_in_some : forall s sc t t0 n m, 
  sol_compress_to s sc ->
  ~ occur n (type_subst t sc) ->
  occur m t ->
  s n = None ->
  s m = Some t0 ->
  ~ occur n t0.
Proof.
  intros.
  destruct H as [H H'].
  assert (sc m <> None). {
    pose proof (H' m).
    rewrite H3 in H4.
    congruence.
  }
  pose proof (some_not_occur_after_subst _ t _ H H4).
  induction t ; simpl in * ; subst .
  - pose proof (H' n0). rewrite H3 in H1.
    rewrite H1 in *.
    intro.
    apply H0.
    eapply none_keep_occur_after_subst ; eauto.
    split ; auto.
  - tauto.
  - destruct H1 ; pose proof H' m as H7; rewrite H3 in H7
    ; apply not_or_and in H0; apply not_or_and in H5; 
    [apply IHt1 | apply IHt2] ; tauto.
  -  destruct H1 ; pose proof H' m as H7; rewrite H3 in H7
  ; apply not_or_and in H0; apply not_or_and in H5; 
  [apply IHt1 | apply IHt2] ; tauto.
Qed.        

Lemma sol_update_keep_no_loop: forall s sc sp n t,
  sol_compress_to s sc ->
  sp = sol_update s n t ->
  sol_no_loop s ->
  s n = None ->
  ~ occur n (type_subst t sc) ->
  sol_no_loop sp.
Proof.
  intros.
  unfold sol_compress_to in H.
  unfold sol_no_loop in *. 
  subst.
  intros.
  unfold sol_update in H0.
  destruct (Z.eq_dec n n0) as [ Hnn0 | Hnn0 ].
  + inversion H0. subst. intro.
    apply H3. eapply none_keep_occur_after_subst ; eauto.
  + apply H1 ; auto.
Qed.

Theorem unify_sound_var: forall n t1 t2 t2' s_pre s_cpre s_post
  (C_s2scpre: sol_compress_to s_pre s_cpre)
  (NoLoop_spre: sol_no_loop s_pre)
  (Finite_s_cpre: sol_finite s_cpre)
  (Heqs_post: s_post = sol_update s_pre n t2')
  (Rt1: repr_rel_node s_pre t1 (TVar n))
  (Rt2: repr_rel_node s_pre t2 t2')
  (* (St1: type_subst t1 s_cpre = TVar n)
  (St2: type_subst t2 s_cpre = t2') *)
  (Occ: not_occur_final s_pre n t2'),
  exists s_cpost,
    sol_compress_to s_post s_cpost /\
    sol_no_loop s_post /\
    sol_finite s_cpost /\
    sol_correct_iter t1 t2 s_cpre s_cpost.
Proof.
  intros.
  remember (sol_c_update s_cpre n (type_subst t2 s_cpre)) as s_cpost.
  exists s_cpost.
  (* prepare some usefull hypothesis *)
  assert (sol_compress_to s_post s_cpost) as C_s2scpost. {
    specialize (sol_c_update_keep_compress_to _ _ _ _ _ C_s2scpre Rt2 Occ) as Hc.
    rewrite Heqs_post, Heqs_cpost.
    apply Hc.
    specialize (repr_rel_node_rhs _ _ _ Rt1) as H.
    destruct H; [ inversion H | ].
    destruct H as [ m [ Heqnm Hspren ] ].
    inversion Heqnm.
    subst m.
    assumption.
  }
  assert (s_cpre n = None) as H_scpre_n. {
    specialize (repr_rel_node_rhs_var _ _ _ Rt1) as Hs_pre_n.
    specialize (proj2 C_s2scpre n) as Hscpre_n.
    rewrite Hs_pre_n in Hscpre_n.
    assumption.
  }
  specialize (repr_rel_subst_same _ _ _ _ C_s2scpre Rt1) as Subst_1.
  specialize (repr_rel_subst_same _ _ _ _ C_s2scpre Rt2) as Subst_2.

  pose proof (proj1 C_s2scpre) as C_scpre.
  specialize (Occ s_cpre C_s2scpre) as Occ_scpre.
  rewrite <- Subst_2 in Occ_scpre.

  (* start prove *)
  intuition.
  2: {
    specialize (sol_update_keep_finite _ n (type_subst t2 s_cpre) Finite_s_cpre) as Fn.
    subst s_cpost.
    assumption.
  }
  + (* sol_no_loop *)
    apply (sol_update_keep_no_loop s_pre s_cpre _ _ _ C_s2scpre Heqs_post); eauto.
    specialize (repr_rel_node_rhs _ _ _ Rt1) as H.
    destruct H; [ inversion H | ].
    destruct H as [ m [ Heqnm Hspren ] ].
    inversion Heqnm.
    subst m.
    assumption.
  + intros sf C_sf.
    intuition.
    - (* 即证明 sol_c_update_tight *)
      eapply (sol_c_update_tight _ _ _ _ _ Heqs_cpost);
      try assumption.
      apply (sol_valid_eq_transity _ t1 _ _); [ | assumption ].
      eapply (sol_refine_keep_valid_eq s_cpre); auto.
      unfold sol_valid_eq.
      auto.
    - (* 这一个分支应当是容易的。只要先证明 s_cpost 满足，再由refine性质即得 *)
      eapply (sol_refine_keep_valid_eq s_cpost); try assumption.
      apply (proj1 C_s2scpost).
      (* 下面只要证明对 s_cpost 成立 *)
      unfold sol_valid_eq.
      specialize (sol_c_update_is_refine_subst _ _ _ _ (proj1 C_s2scpre) H_scpre_n Heqs_cpost) as Subst_p.
      specialize (Subst_p t1) as Subst_p1.
      specialize (Subst_p t2) as Subst_p2.
      unfold type_subst in Subst_1 at 2.
      rewrite H_scpre_n in Subst_1.
      rewrite Subst_1 in Subst_p1.
      rewrite Subst_p1.
      unfold type_subst at 1.
      rewrite Heqs_cpost.
      rewrite <- Heqs_cpost at 1.
      unfold sol_c_update.
      destruct (Z.eq_dec n n); [ | contradiction ].
      rewrite Subst_p2.
      symmetry.
      eapply (subst_not_occur_same _ _ _ _ Heqs_cpost); try assumption.
    - (* 这个分支通过 refine 的传递性进行证明。先要证明 sol_c_update 是 refine *)
      eapply (sol_refine_trantivity _ s_cpost _ (proj1 C_s2scpost) C_sf);
      try assumption.
      rewrite Heqs_cpost.
      apply (sol_c_update_is_refine _ _ _ (proj1 C_s2scpre) H_scpre_n).
Qed.


Theorem unify_soundness: unify_sound1.
Proof.
  red.
  intros.
  revert s_cpre C_spre2scpre NoLoop_spre Finite_scpre.
  induction U; intros;
  pose proof (repr_rel_subst_same _ _ _ _ C_spre2scpre R1) as St1;
  pose proof (repr_rel_subst_same _ _ _ _ C_spre2scpre R2) as St2.
  5: {
    exists s_cpre; intuition.
    intros s_spec.
    intros C_spec.
    intuition.
    unfold sol_valid_eq.
    specialize (H t1) as Ht3; specialize (H t2) as Ht4.
    simpl in St1, St2.
    rewrite St1 in Ht3; rewrite St2 in Ht4.
    rewrite Ht3, Ht4; auto.
  }
  - eapply (unify_sound_var n1 t1 t2 t2' s); auto.
  - specialize (unify_sound_var n2 t2 t1 t1' s s_cpre (sol_update s n2 t1')) as Lem.
    destruct Lem; auto.
    exists x.
    intuition; try assumption.
    apply (sol_correct_iter_swap t2 t1 s_cpre x).
    assumption.
  - specialize (IHU1 s_cpre);
    destruct IHU1 as [s1_c [ IH11 [ IH12 [ IH13 IH14 ] ] ] ]; try tauto.
    specialize (IHU2 s1_c);
    destruct IHU2 as [s2_c [ IH21 [ IH22 [ IH23 IH24 ] ] ] ]; try tauto.
    exists s2_c.
    intuition.
    intro s_spec.
    intros.
    intuition.
    + eapply (unify_induction_sol_tight_TApply _ _ _ _ t1 _ _ t2 _ _ _
        C_spre2scpre (proj1 IH11) (proj1 IH21) H
        St1 St2
        ); auto.
    + pose proof (proj1 IH21) as C_s2c.
      eapply (sol_refine_keep_valid_eq s2_c); auto.
      specialize (IH14 s2_c C_s2c).
      specialize (IH24 s2_c C_s2c).
      destruct IH14 as [ _ IH14 ].
      destruct IH24 as [ _ IH24 ].
      specialize (sol_refine_self s2_c C_s2c) as Hs2c_fine_self.
      specialize (IH24 Hs2c_fine_self).
      destruct IH24 as [ ValidR Hs2c_fine_s1c ].
      specialize (IH14 Hs2c_fine_s1c).
      destruct IH14 as [ ValidL Hs1c_fine_spre ].
      eapply (refine_valid_part_to_full_TApply _ _ _ _ _ _ _ _ Hs1c_fine_spre St1 St2); auto.
    + eapply (sol_refine_trantivity_iter s_cpre s1_c s2_c s_spec); auto.
      apply (proj1 C_spre2scpre).
      apply (proj1 IH11).
      apply (proj1 IH21).
      apply IH14.
      apply IH24.
    (* 这个分支与下一个分支证明完全相同 *)
  - specialize (IHU1 s_cpre);
    destruct IHU1 as [s1_c [ IH11 [ IH12 [ IH13 IH14 ] ] ] ]; try tauto.
    specialize (IHU2 s1_c);
    destruct IHU2 as [s2_c [ IH21 [ IH22 [ IH23 IH24 ] ] ] ]; try tauto.
    exists s2_c.
    intuition.
    intro s_spec.
    intros.
    intuition.
    + eapply (unify_induction_sol_tight_TArrow _ _ _ _ t1 _ _ t2 _ _ _
        C_spre2scpre (proj1 IH11) (proj1 IH21) H
        St1 St2
        ); auto.
    + pose proof (proj1 IH21) as C_s2c.
      eapply (sol_refine_keep_valid_eq s2_c); auto.
      specialize (IH14 s2_c C_s2c).
      specialize (IH24 s2_c C_s2c).
      destruct IH14 as [ _ IH14 ].
      destruct IH24 as [ _ IH24 ].
      specialize (sol_refine_self s2_c C_s2c) as Hs2c_fine_self.
      specialize (IH24 Hs2c_fine_self).
      destruct IH24 as [ ValidR Hs2c_fine_s1c ].
      specialize (IH14 Hs2c_fine_s1c).
      destruct IH14 as [ ValidL Hs1c_fine_spre ].
      eapply (refine_valid_part_to_full_TArrow _ _ _ _ _ _ _ _ Hs1c_fine_spre St1 St2); auto.
    + eapply (sol_refine_trantivity_iter s_cpre s1_c s2_c s_spec); auto.
      apply (proj1 C_spre2scpre).
      apply (proj1 IH11).
      apply (proj1 IH21).
      apply IH14.
      apply IH24.
Qed.
