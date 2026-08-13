Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list.
Local Open Scope Z_scope.
Require Import Lia.
Require Import Coq.Logic.Classical_Prop.
From SimpleC.EE.Applications_human.typeinfer Require Import type_infer_lib.
From SimpleC.EE.Applications_human.typeinfer Require Import repr_subst_prop.


Ltac reduce_refine_to_var :=
  match goal with
  | [ H: sol_refine ?sc ?scf |- _ ] =>
    intros t1; induction t1; [
      | simpl; auto
      | simpl; f_equal; auto
      | simpl; f_equal; auto
    ]
  end.

Lemma sol_refine_self: forall s,
  sol_compressed s ->
  sol_refine s s.
Proof.
  intros.
  intros t1; induction t1; [
      | simpl; auto
      | simpl; f_equal; auto
      | simpl; f_equal; auto
    ].
  unfold type_subst at 1 3.
  destruct (s n) eqn: Hn.
  2: unfold type_subst; rewrite Hn; reflexivity.
  symmetry.
  eapply subst_same_sol_right; auto.
  apply Hn.
Qed.


Lemma correct_iter_impl_refine:
  forall scpre scpost t1 t2,
  sol_compressed scpost ->
  sol_correct_iter t1 t2 scpre scpost ->
  sol_refine scpre scpost.
Proof.
  intros.
  apply H0;
    [ | apply sol_refine_self ];
    assumption.
Qed.


Lemma sol_refine_trantivity:
  forall sc1 sc2 sc3,
  sol_compressed sc2 ->
  sol_compressed sc3 ->
  sol_refine sc1 sc2 ->
  sol_refine sc2 sc3 ->
  sol_refine sc1 sc3.
Proof.
  intros.
  reduce_refine_to_var.
  unfold type_subst at 3.
  destruct (sc1 n) eqn:Hsc1n; [ | reflexivity ].
  specialize (H1 (TVar n)) as Hsc2t.
  pose proof (call_impl_subst _ _ _ Hsc1n) as Subst_sc1_n.
  rewrite Subst_sc1_n in Hsc2t.
  clear Hsc1n Subst_sc1_n.
  specialize (H2 t) as Hsc3t.
  rewrite <- Hsc2t in Hsc3t.
  specialize (H2 (TVar n)) as Hsc3n.
  rewrite <- Hsc3t in Hsc3n.
  assumption.
Qed.


Lemma sol_refine_trantivity_iter:
  forall scpre sc1 sc2 sf,
  forall t11 t12 t21 t22,
  sol_compressed scpre ->
  sol_compressed sc1 ->
  sol_compressed sc2 ->
  sol_compressed sf ->
  sol_correct_iter t11 t21 scpre sc1 ->
  sol_correct_iter t12 t22 sc1 sc2 ->
  sol_refine sc2 sf ->
  sol_refine scpre sf.
Proof.
  intros scpre sc1 sc2 sf t11 t12 t21 t22.
  intros C_scpre C_sc1 C_sc2 C_sf.
  intros CrtL CrtR Rf_sf.
  specialize (correct_iter_impl_refine _ _ _ _ C_sc1 CrtL) as Rf_sc1.
  specialize (correct_iter_impl_refine _ _ _ _ C_sc2 CrtR) as Rf_sc2.
  specialize (sol_refine_trantivity _ _ _ C_sc1 C_sc2 Rf_sc1 Rf_sc2) as Rf_pre_sc2.
  apply (sol_refine_trantivity _ _ _ C_sc2 C_sf Rf_pre_sc2 Rf_sf).
Qed.

Lemma sol_valid_eq_swap: forall t1 t2 sc,
  sol_valid_eq t1 t2 sc <->
  sol_valid_eq t2 t1 sc.
Proof.
  intros.
  unfold sol_valid_eq in *.
  intuition.
Qed.

Lemma sol_correct_iter_swap: forall t1 t2 sc1 sc2,
  sol_correct_iter t1 t2 sc1 sc2 ->
  sol_correct_iter t2 t1 sc1 sc2.
Proof.
  intros.
  intros s C_s.
  specialize (H s C_s).
  specialize (sol_valid_eq_swap t1 t2 s) as Hswap.
  intuition.
Qed.

Lemma sol_finite_compressed: forall s sc,
  sol_compress_to s sc ->
  sol_finite s <-> sol_finite sc.
Proof.
  intros.
  assert (forall n, s n <> None <-> sc n <> None) as Hnone. {
    intros n.
    specialize (proj2 H n) as Hn.
    split; intros.
    + destruct (s n) eqn:Hsn; [ | tauto ].
      rewrite Hn.
      discriminate.
    + destruct (s n) eqn:Hsn; [ discriminate | contradiction ].
  }
  unfold sol_finite.
  split; intros;
  destruct H0 as [ ids H0 ]; exists ids; intros; split; intros;
  specialize (Hnone n) as Hnone_n;
  destruct Hnone_n as [ Hnone_n1 Hnone_n2 ].
  + specialize (H0 n); destruct H0 as [ H0 _ ].
    apply (Hnone_n1 (H0 H1)).
  + specialize (H0 n); destruct H0 as [ _ H0 ].
    apply (H0 (Hnone_n2 H1)).
  + specialize (H0 n); destruct H0 as [ H0 _ ].
    apply (Hnone_n2 (H0 H1)).
  + specialize (H0 n); destruct H0 as [ _ H0 ].
    apply (H0 (Hnone_n1 H1)).
Qed.


Lemma sol_valid_eq_transity: forall t1 t2 t3 sc,
  sol_valid_eq t1 t2 sc ->
  sol_valid_eq t2 t3 sc ->
  sol_valid_eq t1 t3 sc.
Proof.
  intros.
  unfold sol_valid_eq in *.
  rewrite H.
  assumption.
Qed.


(* ********** **********  sol_(c)_update props **********  ********** *)


Lemma sol_update_reverse: forall s n t m,
  n <> m ->
  sol_update s n t m = s m.
Proof.
  intros.
  unfold sol_update.
  destruct (Z.eq_dec n m) eqn: Hnm.
  contradiction.
  reflexivity.
Qed.

Lemma sol_update_reverse_none: forall s n t m,
  sol_update s n t m = None ->
  s m = None /\ n <> m.
Proof.
  intros.
  unfold sol_update in H.
  destruct (Z.eq_dec n m) as [ Hnm | Hnm ].
  discriminate H.
  split;
  assumption.
Qed.




Lemma sol_c_update_is_refine_subst: forall sc scp n t0,
  sol_compressed sc ->
  sc n = None ->
  scp = sol_c_update sc n (type_subst t0 sc) ->
  forall ta,
  type_subst ta scp = type_subst (type_subst ta sc) scp.
Proof.
  intros sc scp n t0.
  intros C_sc Hscn Hscp.
  induction ta.
  3, 4: simpl; f_equal; assumption.
  2: simpl; reflexivity.
  unfold type_subst at 3.
  (* 现在要证明，对于任意的一个变量的解释，直接替换和两次替换相等 *)
  (* 问题其实在与 n0 的解释中是否包含了 n 这个变量 *)
  (* 首先排除 sc n0 没有解释的情况 *)
  destruct (sc n0) eqn:Hscn0; [ | reflexivity ].
  assert (n <> n0) as Hnn0. {
    intros contra.
    subst n0.
    rewrite Hscn in Hscn0.
    inversion Hscn0.
  }
  assert (scp n0 = sol_c_update sc n (type_subst t0 sc) n0) as Hscpn0. {
    rewrite Hscp.
    reflexivity.
  }
  unfold sol_c_update in Hscpn0.
  destruct (Z.eq_dec n n0) as [ a | _ ]; [ contradiction | ].
  rewrite Hscn0 in Hscpn0.
  unfold type_subst at 1.
  rewrite Hscpn0.
  specialize (C_sc n0) as C_sc_n0.
  rewrite Hscn0 in C_sc_n0.
  (* 也许在clear之前，需要给出关于t的一些性质 *)
  clear Hscn0 Hscpn0.
  induction t.
  3, 4:
    simpl;
    f_equal;
    try eapply IHt1; try eapply IHt2;
    intros m;
    specialize (C_sc_n0 m);
    destruct (sc m) eqn:Hscm; try reflexivity;
    simpl in C_sc_n0;
    apply not_or_and in C_sc_n0;
    intuition.
  2: simpl; reflexivity.
  rewrite Hscp.
  unfold sol_c_update.
  simpl.
  destruct (Z.eq_dec n n1) as [ Hnn1 | Hnn1 ]; [ reflexivity | ].
  destruct (sc n1) eqn:Hscn1; [ | reflexivity ].
  specialize (C_sc_n0 n1).
  rewrite Hscn1 in C_sc_n0.
  simpl in C_sc_n0.
  contradiction.
Qed.



Lemma unfold_valid_eq_var: forall s n t
  (C_s: sol_compressed s)
  (Valid: sol_valid_eq (TVar n) t s),
  (s n = None /\ exists m, t = TVar m /\ (s m = Some (TVar n) \/ (m = n))) \/
  s n = Some(type_subst t s).
Proof.
  intros.
  unfold sol_valid_eq in Valid.
  unfold type_subst in Valid at 1.
  destruct (s n) eqn: Hsn.
  + right; f_equal; assumption.
  + left.
    intuition.
    destruct t; inversion Valid.
    rename n0 into m.
    exists m.
    intuition.
    destruct (s m) eqn: Hsm; try subst t; auto.
    right.
    inversion H0; reflexivity.
Qed.


Lemma sol_c_update_subst: forall s sp n t n1 tn1,
	sol_compressed s ->
	sp = sol_c_update s n (type_subst t s) ->
	s n = None ->
	~occur n (type_subst t s) ->
	n <> n1 ->
	s n1 = Some (type_subst tn1 s) ->
	sp n1 = Some (type_subst tn1 sp).
Proof.
	intros s sp n t n1 tn1.
	intros C_s Hsp Hsn Occ_t Hnn1 Hsn1.

	specialize (sol_c_update_is_refine_subst s sp n t) as Hsubst.
	specialize (Hsubst C_s Hsn Hsp (TVar n1)).

  unfold type_subst in Hsubst at 1.
  remember (sp n1) as t_spn1.

  rewrite Hsp in Heqt_spn1.
  unfold sol_c_update in Heqt_spn1.
  destruct (Z.eq_dec n n1) as [ a | _ ]; [ contradiction | ].
  rewrite Hsn1 in Heqt_spn1.
  subst t_spn1.
  f_equal.

  remember (type_subst (TVar n1) s) as t_sn1.
  unfold type_subst in Heqt_sn1.
  rewrite Hsn1 in Heqt_sn1.
  subst t_sn1.
  rewrite Hsubst.

  symmetry.
  eapply (sol_c_update_is_refine_subst _ _ _ _ C_s Hsn Hsp).
Qed.


Lemma sol_c_update_is_refine: forall sc n t,
  sol_compressed sc ->
  sc n = None ->
  (* ~occur n t ->  *) (* not need *)
  sol_refine sc (sol_c_update sc n (type_subst t sc)).
Proof.
  intros.
  intros t1.
  induction t1.
  3, 4: simpl; f_equal; assumption.
  2: simpl; reflexivity.
  rename n0 into n1.
  remember (sol_c_update sc n (type_subst t sc)) as scp.
  unfold type_subst at 3.
  destruct (sc n1) eqn:Hscn1; [ | tauto ].
  pose proof (sol_c_update_is_refine_subst _ _ _ _ H H0 Heqscp (TVar n1)).
  pose proof (call_impl_subst _ _ _ Hscn1).
  rewrite H2 in H1.
  assumption.
Qed.

Lemma sol_c_update_keep_compressed: forall s sc n t1 t2,
  sol_compress_to s sc ->
  repr_rel_node s t1 t2 ->
  not_occur_final s n t2 ->
  s n = None ->
  sol_compressed (sol_c_update sc n (type_subst t1 sc)).
Proof.
  intros s sc n t1 t2.
  intros C_s2sc Rel Occ Hsn.
  specialize (repr_rel_subst_same _ _ _ _ C_s2sc Rel) as Hsubst.
  (* use the t2 might be easier *)
  rewrite Hsubst.
  intros n1 n2.
  unfold sol_c_update.
  destruct (Z.eq_dec n n1) as [ Hnn1 | Hnn1 ];
  destruct (Z.eq_dec n n2) as [ Hnn2 | Hnn2 ].
  + subst n1 n2.
    apply (Occ sc C_s2sc).
  + subst n1.
    destruct (sc n2) eqn:Hscn2; [ | tauto ].
    destruct C_s2sc as [ C_sc C_s2sc ].
    apply (some_not_occur_after_subst sc t2 n2 C_sc).
    (* specialize (C_s2sc n2) as Hscn2. *)
    (* rewrite Hsn2 in Hscn2. *)
    rewrite Hscn2.
    discriminate.
  + subst n2.
    destruct (sc n1) eqn:Hscn1; [ | tauto ].
    specialize (Occ sc C_s2sc).
    destruct C_s2sc as [ C_sc C_s2sc ].
    specialize (subst_same_sol_right sc _ _ C_sc Hscn1) as Ht.
    (* specialize (some_not_occur_after_subst_var) as Hnone.
    specialize (Hnone sc t t2 n n C_sc Ht). *)
    specialize (self_not_occur_after_subst_var sc t t2 n) as Hnone.
    specialize (Hnone C_sc Ht).
    apply Hnone, Occ.
    specialize (C_s2sc n).
    rewrite Hsn in C_s2sc.
    assumption.
  + destruct (sc n1) eqn:Hscn1, (sc n2) eqn:Hscn2;
    try tauto.
    destruct C_s2sc as [ C_sc C_s2sc ].
    specialize (subst_same_sol_right sc _ _ C_sc Hscn1) as Ht.
    specialize (some_not_occur_after_subst_var sc t t2 n n2) as Hnone.
    apply (Hnone C_sc Ht).
    - specialize (C_s2sc n).
      rewrite Hsn in C_s2sc.
      assumption.
    - rewrite Hscn2.
      discriminate.
Qed.

Lemma sol_c_update_keep_compress_to: forall s_pre s_cpre n t1 t2,
  sol_compress_to s_pre s_cpre ->
  repr_rel_node s_pre t1 t2 ->
  not_occur_final s_pre n t2 ->
  s_pre n = None ->
  sol_compress_to (sol_update s_pre n t2) (sol_c_update s_cpre n (type_subst t1 s_cpre)).
Proof.
  intros.
  split.
  apply (sol_c_update_keep_compressed s_pre s_cpre n t1 t2 H H0 H1 H2).
  remember (sol_c_update s_cpre n (type_subst t1 s_cpre)) as s_cpost.
  remember (sol_update s_pre n t2) as s_post.
  (*
    下面需要证明对 s_post --compress_to--> s_cpost
		基本想法：分类讨论，规约到 s_cpre 和 s_cpost 上
  *)
  intros n1.
  destruct (s_post n1) eqn:Hsnn1.
  2: {
    (* 当 s_post n1 = None *)
    rewrite Heqs_post in Hsnn1.
    specialize (sol_update_reverse_none s_pre n t2 n1 Hsnn1) as Hsn1.
    destruct Hsn1 as [ Hsn1 Hnn1 ].
    specialize (proj2 H n1) as Hcpre_n1.
    rewrite Hsn1 in Hcpre_n1.
    rewrite Heqs_cpost.
    unfold sol_c_update.
    destruct (Z.eq_dec n n1); [ contradiction | ].
    rewrite Hcpre_n1.
    reflexivity.
  }
  (* 当 s_post n1 = Some(t), 需要根据 n1 =? n 进行分类讨论 *)
  rewrite Heqs_post in Hsnn1.
  unfold sol_update.
  unfold sol_update in Hsnn1.
  destruct (Z.eq_dec n n1) as [ Hnn1 | Hnn1 ].
  + (* n = n1 *)
    inversion Hsnn1.
    subst t2 n1.
    clear Hsnn1.
    rewrite Heqs_cpost.
    rewrite <- Heqs_cpost at 1.
    unfold sol_c_update.
    destruct (Z.eq_dec n n) as [ _ | a ]; [ | contradiction ].
    f_equal.

    specialize (repr_rel_subst_same s_pre s_cpre t1 t) as Hsubst.
    specialize (Hsubst H H0).
    rewrite Hsubst in *.

    clear t1 s_post H0 Heqs_post Hsubst.

    specialize (H1 s_cpre H) as Occ.
    remember (type_subst t s_cpre) as tn.
    symmetry in Heqtn.
    specialize (subst_same_twice s_cpre t tn (proj1 H) Heqtn) as Hsubst2.

    specialize (subst_keep_same_update s_cpre n tn tn) as Lem.
    specialize (Lem (proj1 H) Occ Hsubst2 Occ Hsubst2).
    rewrite <- Heqs_cpost in Lem.
    rewrite <- Lem.

		rewrite <- Heqtn.
		symmetry.
		eapply (sol_c_update_is_refine_subst _ _ n t).
		apply (proj1 H).
		specialize (proj2 H n) as Hcpre_n.
		rewrite H2 in Hcpre_n.
		assumption.
		rewrite <- Heqtn in Heqs_cpost.
		assumption.
  + (* n <> n1 *)
    specialize (proj2 H n1) as Hscpre_n1.
    rewrite Hsnn1 in Hscpre_n1.
		specialize (proj2 H n) as Hscpre_n.
		rewrite H2 in Hscpre_n.
    eapply (sol_c_update_subst s_cpre _ n t1);
    try assumption.
    apply (proj1 H).
    specialize (H1 s_cpre H).
    specialize (repr_rel_subst_same s_pre s_cpre t1 t2) as Hsubst.
    specialize (Hsubst H H0).
    rewrite Hsubst.
    assumption.
Qed.


(* 在修改了refine的定义后，这个引理所说的事情实际上就是refine的定义 *)
Lemma sol_refine_subst: forall sc scf,
  sol_refine sc scf ->
  forall t,
  type_subst t scf = type_subst (type_subst t sc) scf.
Proof.
  auto.
Qed.


Lemma refine_over_type_subst_var: forall sc scf n t
  (Rf: sol_refine sc scf)
  (C_sc: sol_compressed sc)
  (Hscfn: scf n = Some (type_subst (type_subst t sc) scf)),
  forall m t1
  (Hscm: sc m = Some t1),
  type_subst (TVar m) scf = type_subst (type_subst_var t1 n (type_subst t sc)) scf.
Proof.
  intros.
  specialize (Rf (TVar m)) as Hscfm.
  pose proof (call_impl_subst _ _ _ Hscm) as Subst_sc_m.
  pose proof (call_impl_subst _ _ _ Hscfn) as Subst_scf_n.
  rewrite Subst_sc_m in Hscfm.
  rewrite Hscfm.
  clear Hscm Hscfm Subst_sc_m.
  induction t1.
  3, 4: simpl; f_equal; auto.
  2: simpl; reflexivity.
  rename n0 into n1.
  unfold type_subst_var.
  destruct (Z.eq_dec n n1) as [ Hnn1 | Hnn1 ].
  + subst n1. rewrite Subst_scf_n. reflexivity.
  + reflexivity.
Qed.



Lemma sol_c_update_tight_normal: forall sc scp scf n t
  (Hscp: scp = sol_c_update sc n (type_subst t sc))
  (C_sc: sol_compressed sc)
  (Occ_n: ~occur n (type_subst t sc))
  (Hsn: sc n = None)
  (C_scf: sol_compressed scf)
  (Rf_scf: sol_refine sc scf)
  (Hscfn: scf n = Some(type_subst t scf)),
  sol_refine scp scf.
Proof.
  intros.
  reduce_refine_to_var.
  rename n0 into n1.
  pose proof (sol_refine_subst _ _ Rf_scf t) as Subst_t.
  assert (scf n = Some(type_subst (type_subst t sc) scf)). {
    rewrite Hscfn. f_equal. assumption.
  }
  unfold type_subst at 3.
  destruct (Z.eq_dec n n1) as [ Hnn1 | Hnn1 ];
  rewrite Hscp;
  unfold sol_c_update.
  1: {
    subst n1.
    destruct (Z.eq_dec n n) as [ _ | a ]; [ | contradiction ].
    eapply call_impl_subst; assumption.
  }
  destruct (Z.eq_dec n n1) as [ a | _ ]; [ contradiction | ].
  destruct (sc n1) eqn:Hscn1; [ | tauto ].
  eapply refine_over_type_subst_var; auto.
Qed.

Lemma sol_c_update_tight_var_to_var: forall sc scp scf n m
  (C_sc: sol_compressed sc)
  (C_scf: sol_compressed scf)
  (H_scp: scp = sol_c_update sc n (TVar m))
  (Hscn: sc n = None)
  (Hscm: sc m = None)
  (Rf_scf: sol_refine sc scf)
  (Hscfm: scf m = Some (TVar n)),
  sol_refine scp scf.
  (* forall n1,
  type_subst (TVar n1) scf = type_subst (type_subst (TVar n1) sc) scf. *)
Proof.
  intros.
  reduce_refine_to_var.
  rename n0 into n1.
  unfold type_subst at 3.
  destruct (scp n1) eqn:Hscpn1; [ | tauto ].
  rewrite H_scp in Hscpn1.
  unfold sol_c_update in Hscpn1.
  destruct (Z.eq_dec n n1) as [ Hnn1 | Hnn1 ].
  1: {
    inversion Hscpn1.
    subst t n1.
    clear Hscpn1.
    specialize (C_scf m n) as Hscfmn.
    rewrite Hscfm in Hscfmn.
    destruct (scf n) eqn:Hscfn; [ congruence | ].
    unfold type_subst; rewrite Hscfm, Hscfn; reflexivity.
  }
  destruct (sc n1) eqn:Hsc_n1; inversion Hscpn1.
  clear Hscpn1.
  pose proof (call_impl_subst _ _ _ Hsc_n1) as Subst_sc_n1.
  specialize (Rf_scf (TVar n1)) as Hscfn1.
  rewrite Subst_sc_n1 in Hscfn1.
  rewrite Hscfn1.

  clear n1 t Hnn1 Hsc_n1 H0 Subst_sc_n1 Hscfn1.
  clear scp C_sc H_scp Hscn.
  pose proof (call_impl_subst _ _ _ Hscfm) as Subst_sc_m.
  induction t0; [
    | simpl; reflexivity
    | simpl; f_equal; auto
    | simpl; f_equal; auto
  ].
  unfold type_subst_var.
  destruct (Z.eq_dec n n0) as [ Hmn0 | Hmn0 ].
  + subst n0.
    specialize (C_scf m n) as Hscfmn.
    rewrite Hscfm in Hscfmn.
    destruct (scf n) eqn:Hscfn; [ congruence | ].
    unfold type_subst; rewrite Hscfm, Hscfn; reflexivity.
  + reflexivity.
Qed.


Lemma sol_c_update_tight_abnormal: forall sc scp scf n m
  (Hscp: scp = sol_c_update sc n (type_subst (TVar m) sc))
  (C_sc: sol_compressed sc)
  (Occ_n: ~occur n (type_subst (TVar m) sc))
  (Hsn: sc n = None)
  (C_scf: sol_compressed scf)
  (Rf_scf: sol_refine sc scf)
  (Hscfn: scf m = Some (TVar n) \/ m = n),
  sol_refine scp scf.
Proof.
  intros.
  destruct Hscfn as [ Hscfn | Hmn ].
  2: {
    subst m.
    simpl in Occ_n.
    rewrite Hsn in Occ_n.
    congruence.
  }
  (* 在这个分支中，scp实质上是令sc[n]=m或者m',而scf是至少令sc[m]=n或令sc[m']=n *)
  (* 下面将排除其他情况 *)
  specialize (Rf_scf (TVar m)) as Hscfm.
  unfold type_subst in Hscp.
  destruct (sc m) eqn:Hscm.
  2: {
    eapply (sol_c_update_tight_var_to_var _ _ _ _ _ C_sc C_scf Hscp);
    assumption.
  }
  pose proof (call_impl_subst _ _ _ Hscm) as Subst_sc_m.
  rewrite Subst_sc_m in Hscfm.
  unfold type_subst in Hscfm at 1.
  rewrite Hscfn in Hscfm.
  inversion Hscfm.
  destruct t; inversion H0.
  destruct (scf n0) eqn:Hscfn0.
  2: {
    inversion H1.
    subst n0.
    unfold type_subst in Occ_n.
    rewrite Hscm in Occ_n.
    congruence.
  }
  subst t.
  eapply (sol_c_update_tight_var_to_var _ _ _ _ _ C_sc C_scf Hscp);
  try assumption.
  specialize (C_sc m n0).
  rewrite Hscm in C_sc.
  destruct (sc n0) eqn:Hscn0; try reflexivity.
  congruence.
Qed.


Lemma sol_c_update_tight: forall sc scp scf n t
  (Hscp: scp = sol_c_update sc n (type_subst t sc))
  (C_sc: sol_compressed sc)
  (Occ_n: ~occur n (type_subst t sc))
  (Hsn: sc n = None)
  (C_scf: sol_compressed scf)
  (Rf_scf: sol_refine sc scf)
  (Veq: sol_valid_eq (TVar n) t scf),
  sol_refine scp scf.
Proof.
  intros.
  pose proof (sol_refine_subst _ _ Rf_scf).
  pose proof (unfold_valid_eq_var _ _ _ C_scf Veq).
  destruct H0 as [ Abnormal | Normal ].
  2: eapply (sol_c_update_tight_normal _ _ _ _ _ Hscp); assumption.
  destruct Abnormal as [ Hscfn [ m [ Htm Hscfm ] ] ].
  subst t.
  eapply (sol_c_update_tight_abnormal).
  apply Hscp.
  1,2,3,4,5,6: auto.
Qed.
