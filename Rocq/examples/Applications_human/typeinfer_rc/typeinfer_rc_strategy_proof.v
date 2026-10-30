From Coq Require Import ZArith List String Lia.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc typeinfer_rc_strategy_goal.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string_scope.

(* Strategy-local facts: the representation layer does not import the VC lib. *)
Lemma strategy_count_live : forall M p,
  rc_valid M -> 0 < rc_count M p -> exists n, node_at M p n.
Proof.
  intros M p [Hv Hp] Hpos.
  destruct (RCMap.nodes M p) as [n|] eqn:Hn.
  - exists n; exact Hn.
  - destruct Hv as [_ [_ [_ [_ [_ [Hd _]]]]]].
    specialize (Hd p Hn); unfold rc_count in Hpos; type_rcmap_reduce; lia.
Qed.

Lemma strategy_reserved_live : forall M p,
  rc_valid M -> 0 < rc_reserved M p -> exists n, node_at M p n.
Proof.
  intros M p [[Hex [Hcl [Hac [Hr [Hl [Hd Hrs]]]]]] Hp] Hres.
  destruct (RCMap.nodes M p) as [n|] eqn:Hn; [exists n; exact Hn|].
  specialize (Hd p Hn); specialize (Hrs p); unfold rc_reserved in Hres;
    type_rcmap_reduce; lia.
Qed.

(* Resource extraction is guarded by a real freshness premise before the
   strategy changes the world. No contradictory-wand fallback is needed. *)
Lemma strategy_field_read : forall M p n slot L ty a value,
  node_at M p n ->
  field_fresh (p,slot) L ->
  store_type_field M p n slot = poly_store ty a value ->
  store_world_missing M L |--
    store_world_missing M ((p,slot)::L) **
    (ALL v : front_end_type_value ty, TT && “v = value” && emp -*
       TT && emp ** poly_store ty a v).
Proof.
  intros M p n slot L ty a value Hn Hfresh Hfield.
  sep_apply (store_world_missing_split M L p n slot Hn Hfresh).
  rewrite Hfield.
  cancel (store_world_missing M ((p,slot)::L)).
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; entailer!.
Qed.

Lemma strategy_field_write : forall M p n slot L ty a value,
  node_at M p n ->
  field_fresh (p,slot) L ->
  store_type_field M p n slot = poly_store ty a value ->
  store_world_missing M L |--
    store_world_missing M ((p,slot)::L) **
    (TT && emp -* TT && emp ** poly_undef_store ty a).
Proof.
  intros M p n slot L ty a value Hn Hfresh Hfield.
  sep_apply (store_world_missing_split M L p n slot Hn Hfresh).
  rewrite Hfield.
  cancel (store_world_missing M ((p,slot)::L)).
  apply_sepcon_adjoint. entailer!.
  apply poly_store_poly_undef_store.
Qed.

Lemma typeinfer_rc_strategy0_correctness : typeinfer_rc_strategy0.
Proof.
  pre_process_default.
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
  apply store_world_missing_nil.
Qed.

Lemma typeinfer_rc_strategy4_correctness : typeinfer_rc_strategy4.
Proof.
  pre_process_default.
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
  subst; entailer!.
  apply derivable1s_allp_r; intro m.
  rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
  subst; entailer!.
Qed.

Lemma typeinfer_rc_strategy6_correctness : typeinfer_rc_strategy6.
Proof.
  unfold typeinfer_rc_strategy6; intros L p M n; pre_process_default.
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
  unfold field_fresh, field_key in *.
  fold (store_type_field M p n Tag).
  sep_apply (store_world_missing_merge M L p n Tag H H0).
  cancel.
Qed.

Lemma typeinfer_rc_strategy17_correctness : typeinfer_rc_strategy17.
Proof.
  unfold typeinfer_rc_strategy17; intros v name M unused p; pre_process_default.
  subst v.
  unfold payload_keys; cbn [node_tag].
  csimpl.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!. subst N.
  eapply derivable1_trans; [|apply (proj1 (store_world_missing_nil M))].
  eapply derivable1_trans; [|apply (store_world_missing_merge M [] p (Node 3 name unused) Payload0 H ltac:(simpl; tauto))].
  unfold store_type_field; cbn [node_tag node_a]. csimpl. cancel.
Qed.

Lemma typeinfer_rc_strategy34_correctness : typeinfer_rc_strategy34.
Proof.
  pre_process_default. subst.
  entailer!. Intros_r v. apply_sepcon_adjoint. entailer!; subst; entailer!.
Qed.

Lemma typeinfer_rc_strategy35_correctness : typeinfer_rc_strategy35.
Proof.
  pre_process_default. subst.
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
  apply poly_store_poly_undef_store.
Qed.

Lemma typeinfer_rc_strategy7_correctness : typeinfer_rc_strategy7.
Proof.
  unfold typeinfer_rc_strategy7; intros M; pre_process_default.
  sep_apply (proj2 (store_world_missing_nil M)).
  cancel (store_world_missing M []).
  Intros_r ty v a. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy8_correctness : typeinfer_rc_strategy8.
Proof.
  unfold typeinfer_rc_strategy8; intros M; pre_process_default.
  sep_apply (proj2 (store_world_missing_nil M)).
  cancel (store_world_missing M []).
  Intros_r ty a. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy33_correctness : typeinfer_rc_strategy33.
Proof.
  unfold typeinfer_rc_strategy33; intros p unused name M; pre_process_default.
  sep_apply (store_world_missing_split M [] p (Node 3 name unused) Payload0 H ltac:(simpl; tauto)).
  unfold store_type_field, payload_keys; cbn [node_tag node_a].
  csimpl.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy20_correctness : typeinfer_rc_strategy20.
Proof.
  unfold typeinfer_rc_strategy20; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy21_correctness : typeinfer_rc_strategy21.
Proof.
  unfold typeinfer_rc_strategy21; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  apply_sepcon_adjoint. entailer!. csimpl. apply store_int_undef_store_int.
Qed.

Lemma typeinfer_rc_strategy22_correctness : typeinfer_rc_strategy22.
Proof.
  unfold typeinfer_rc_strategy22; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy23_correctness : typeinfer_rc_strategy23.
Proof.
  unfold typeinfer_rc_strategy23; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  apply_sepcon_adjoint. entailer!. csimpl. apply store_int_undef_store_int.
Qed.

Lemma typeinfer_rc_strategy24_correctness : typeinfer_rc_strategy24.
Proof.
  unfold typeinfer_rc_strategy24; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy25_correctness : typeinfer_rc_strategy25.
Proof.
  unfold typeinfer_rc_strategy25; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  apply_sepcon_adjoint. entailer!. csimpl. apply store_ptr_undef_store_ptr.
Qed.

Lemma typeinfer_rc_strategy26_correctness : typeinfer_rc_strategy26.
Proof.
  unfold typeinfer_rc_strategy26; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload1) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload1 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload1)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy27_correctness : typeinfer_rc_strategy27.
Proof.
  unfold typeinfer_rc_strategy27; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload1) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload1 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload1)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  apply_sepcon_adjoint. entailer!. csimpl. apply store_ptr_undef_store_ptr.
Qed.

Lemma typeinfer_rc_strategy28_correctness : typeinfer_rc_strategy28.
Proof.
  unfold typeinfer_rc_strategy28; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy29_correctness : typeinfer_rc_strategy29.
Proof.
  unfold typeinfer_rc_strategy29; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  apply_sepcon_adjoint. entailer!. csimpl. apply store_ptr_undef_store_ptr.
Qed.

Lemma typeinfer_rc_strategy30_correctness : typeinfer_rc_strategy30.
Proof.
  unfold typeinfer_rc_strategy30; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload1) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload1 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload1)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy31_correctness : typeinfer_rc_strategy31.
Proof.
  unfold typeinfer_rc_strategy31; intros n M p L; pre_process_default.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload1) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload1 H Hfresh).
  unfold store_type_field; rewrite H1.
  entailer!.
  cancel (store_world_missing M ((p,Payload1)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  apply_sepcon_adjoint. entailer!. csimpl. apply store_ptr_undef_store_ptr.
Qed.

Lemma typeinfer_rc_strategy5_correctness : typeinfer_rc_strategy5.
Proof.
  unfold typeinfer_rc_strategy5; intros L p M n; pre_process_default.
  sep_apply (strategy_field_read M p n Tag L FET_int
    (&(p # "atype" ->ₛ "t")) (node_tag n) H H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy9_correctness : typeinfer_rc_strategy9.
Proof.
  unfold typeinfer_rc_strategy9; intros L p M n; pre_process_default.
  sep_apply (strategy_field_read M p n RefCount L FET_int
    (&(p # "atype" ->ₛ "refcnt")) (rc_count M p) H H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy10_correctness : typeinfer_rc_strategy10.
Proof.
  unfold typeinfer_rc_strategy10; intros L p M n; pre_process_default.
  sep_apply (strategy_field_write M p n RefCount L FET_int
    (&(p # "atype" ->ₛ "refcnt")) (rc_count M p) H H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy13_correctness : typeinfer_rc_strategy13.
Proof.
  unfold typeinfer_rc_strategy13; intros L p M n; pre_process_default.
  sep_apply (strategy_field_write M p n Tag L FET_int
    (&(p # "atype" ->ₛ "t")) (node_tag n) H H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy11_correctness : typeinfer_rc_strategy11.
Proof.
  unfold typeinfer_rc_strategy11; intros M p L; pre_process_default.
  destruct (strategy_count_live M p H H1) as [n Hn].
  Exists n.
  sep_apply (strategy_field_read M p n RefCount L FET_int
    (&(p # "atype" ->ₛ "refcnt")) (rc_count M p) Hn H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy12_correctness : typeinfer_rc_strategy12.
Proof.
  unfold typeinfer_rc_strategy12; intros M p L; pre_process_default.
  destruct (strategy_count_live M p H H1) as [n Hn].
  Exists n.
  sep_apply (strategy_field_write M p n RefCount L FET_int
    (&(p # "atype" ->ₛ "refcnt")) (rc_count M p) Hn H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy14_correctness : typeinfer_rc_strategy14.
Proof.
  unfold typeinfer_rc_strategy14; intros M p L; pre_process_default.
  destruct (strategy_reserved_live M p H H1) as [n Hn].
  Exists n.
  sep_apply (strategy_field_read M p n RefCount L FET_int
    (&(p # "atype" ->ₛ "refcnt")) (rc_count M p) Hn H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy15_correctness : typeinfer_rc_strategy15.
Proof.
  unfold typeinfer_rc_strategy15; intros M p L; pre_process_default.
  destruct (strategy_reserved_live M p H H1) as [n Hn].
  Exists n.
  sep_apply (strategy_field_write M p n RefCount L FET_int
    (&(p # "atype" ->ₛ "refcnt")) (rc_count M p) Hn H0 eq_refl).
  unfold field_key. entailer!.
Qed.

(* Post saturation only adds immutable decoding facts. The absence guard is
   operational and is deliberately not a premise of these soundness proofs. *)
Lemma typeinfer_rc_strategy36_correctness : typeinfer_rc_strategy36.
Proof.
  unfold typeinfer_rc_strategy36; intros p tr M N; pre_process_default.
  assert (store_type N p tr) by (eapply decode_type_preserves; eauto).
  entailer!; try apply_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy37_correctness : typeinfer_rc_strategy37.
Proof.
  unfold typeinfer_rc_strategy37; intros p n M N; pre_process_default.
  assert (node_at N p n).
  { exact (proj1 H p n H0). }
  entailer!; try apply_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy38_correctness : typeinfer_rc_strategy38.
Proof.
  unfold typeinfer_rc_strategy38; intros p tr M N L; pre_process_default.
  assert (store_type N p tr) by (eapply decode_type_preserves; eauto).
  entailer!; try apply_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy39_correctness : typeinfer_rc_strategy39.
Proof.
  unfold typeinfer_rc_strategy39; intros p n M N L; pre_process_default.
  assert (node_at N p n).
  { exact (proj1 H p n H0). }
  entailer!; try apply_sepcon_adjoint; entailer!.
Qed.

(* Shallow decoding facts used by access-directed rules, not new semantics. *)
Lemma strategy_decode_node : forall M p tr,
  store_type M p tr -> exists n, node_at M p n /\ 0 <= node_tag n <= 3.
Proof.
  intros M p tr; destruct tr; cbn; intros H;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: eexists; split; [eassumption|cbn; lia].
Qed.

Lemma strategy_decode_var : forall M p tr n,
  store_type M p tr -> node_at M p n -> node_tag n = 3 ->
  tr = TVar (node_a n) /\ n = Node 3 (node_a n) 0.
Proof.
  intros M p tr n Hd Hn Htag; destruct tr; cbn in Hd;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes _ _ = Some (Node _ _ _) |- _ =>
      rewrite H in Hn end;
    inversion Hn; subst; cbn in Htag; try discriminate; split; reflexivity.
Qed.

Lemma strategy_decode_arrow : forall M p tr n,
  store_type M p tr -> node_at M p n -> node_tag n = 1 ->
  exists a b, tr = TArrow a b /\
    store_type M (node_a n) a /\ store_type M (node_b n) b.
Proof.
  intros M p tr n Hd Hn Htag; destruct tr; cbn in Hd;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes _ _ = Some (Node _ _ _) |- _ =>
      rewrite H in Hn end;
    inversion Hn; subst; cbn in Htag; try discriminate; eauto 8.
Qed.

Lemma strategy_decode_apply : forall M p tr n,
  store_type M p tr -> node_at M p n -> node_tag n = 2 ->
  exists a b, tr = TApply a b /\
    store_type M (node_a n) a /\ store_type M (node_b n) b.
Proof.
  intros M p tr n Hd Hn Htag; destruct tr; cbn in Hd;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes _ _ = Some (Node _ _ _) |- _ =>
      rewrite H in Hn end;
    inversion Hn; subst; cbn in Htag; try discriminate; eauto 8.
Qed.

Lemma typeinfer_rc_strategy40_correctness : typeinfer_rc_strategy40.
Proof.
  unfold typeinfer_rc_strategy40; intros L p M tr; pre_process_default.
  destruct (strategy_decode_node M p tr H) as [n [Hn [Hlo Hhi]]].
  Exists n.
  sep_apply (strategy_field_read M p n Tag L FET_int
    (&(p # "atype" ->ₛ "t")) (node_tag n) Hn H0 eq_refl).
  unfold field_key. entailer!.
Qed.

Lemma typeinfer_rc_strategy41_correctness : typeinfer_rc_strategy41.
Proof.
  unfold typeinfer_rc_strategy41; intros n p tr M; pre_process_default.
  destruct (strategy_decode_var M p tr n H H0 H2) as [Ht Hnode].
  assert (Hrange : 0 <= node_a n < 100).
  { destruct H1 as [_ Hv]. specialize (Hv p n H0).
    unfold payload_valid in Hv. tauto. }
  assert (Hcanonical : node_at M p (Node 3 (node_a n) 0)) by congruence.
  sep_apply (store_world_missing_split M [] p n Payload0 H0 ltac:(simpl; tauto)).
  unfold store_type_field; rewrite H2.
  unfold payload_keys; cbn [node_tag]; csimpl.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy43_correctness : typeinfer_rc_strategy43.
Proof.
  pre_process_default. entailer!.
  Intros_r out N. apply_sepcon_adjoint. entailer!; subst; entailer!.
Qed.

Lemma typeinfer_rc_strategy46_correctness : typeinfer_rc_strategy46.
Proof.
  unfold typeinfer_rc_strategy46; intros M; pre_process_default.
  entailer!; subst; entailer!.
  apply store_world_missing_nil.
Qed.

Lemma typeinfer_rc_strategy44_correctness : typeinfer_rc_strategy44.
Proof.
  unfold typeinfer_rc_strategy44; intros n M tr p L; pre_process_default.
  destruct (strategy_decode_arrow M p tr n H H0 H2) as [a [b [Ht [Ha Hb]]]].
  Exists a b.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H0 Hfresh).
  unfold store_type_field; rewrite H2.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy45_correctness : typeinfer_rc_strategy45.
Proof.
  unfold typeinfer_rc_strategy45; intros n M tr p L; pre_process_default.
  destruct (strategy_decode_apply M p tr n H H0 H2) as [a [b [Ht [Ha Hb]]]].
  Exists a b.
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H0 Hfresh).
  unfold store_type_field; rewrite H2.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.

Lemma typeinfer_rc_strategy42_correctness : typeinfer_rc_strategy42.
Proof.
  unfold typeinfer_rc_strategy42; intros x n M p L; pre_process_default.
  subst x.
  assert (Hfield : store_type_field M p n Tag = poly_store FET_int (&(p # "atype" ->ₛ "t")) (node_tag n)).
  { reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Tag) L) by assumption.
  fold (store_type_field M p n Tag).
  sep_apply (store_world_missing_merge M L p n Tag H Hfresh).
  entailer!.
  Intros_r v q. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy47_correctness : typeinfer_rc_strategy47.
Proof.
  unfold typeinfer_rc_strategy47; intros v n L M p q; pre_process_default.
  subst q v.
  assert (Hfield : store_type_field M p n Tag = poly_store FET_int (&(p # "atype" ->ₛ "t")) (node_tag n)).
  { reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Tag) L) by assumption.
  fold (store_type_field M p n Tag).
  sep_apply (store_world_missing_merge M L p n Tag H Hfresh).
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy48_correctness : typeinfer_rc_strategy48.
Proof.
  unfold typeinfer_rc_strategy48; intros n q p M L v; pre_process_default.
  subst q v.
  assert (Hfield : store_type_field M p n Payload0 = poly_store FET_ptr (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) (node_a n)).
  { unfold store_type_field; rewrite H3; reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  assert (Hclose : (&( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from") # Ptr |-> (node_a n)) **
      store_world_missing M ((p,Payload0)::L) |-- store_world_missing M L).
  { eapply derivable1_trans; [|apply (store_world_missing_merge M L p n Payload0 H Hfresh)].
    unfold store_type_field; rewrite H3; csimpl; cancel; reflexivity. }
  sep_apply Hclose.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy49_correctness : typeinfer_rc_strategy49.
Proof.
  unfold typeinfer_rc_strategy49; intros n q p M L v; pre_process_default.
  subst q v.
  assert (Hfield : store_type_field M p n Payload1 = poly_store FET_ptr (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) (node_b n)).
  { unfold store_type_field; rewrite H3; reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload1) L) by assumption.
  assert (Hclose : (&( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to") # Ptr |-> (node_b n)) **
      store_world_missing M ((p,Payload1)::L) |-- store_world_missing M L).
  { eapply derivable1_trans; [|apply (store_world_missing_merge M L p n Payload1 H Hfresh)].
    unfold store_type_field; rewrite H3; csimpl; cancel; reflexivity. }
  sep_apply Hclose.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy50_correctness : typeinfer_rc_strategy50.
Proof.
  unfold typeinfer_rc_strategy50; intros n q p M L v; pre_process_default.
  subst q v.
  assert (Hfield : store_type_field M p n Payload0 = poly_store FET_ptr (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) (node_a n)).
  { unfold store_type_field; rewrite H3; reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  assert (Hclose : (&( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn") # Ptr |-> (node_a n)) **
      store_world_missing M ((p,Payload0)::L) |-- store_world_missing M L).
  { eapply derivable1_trans; [|apply (store_world_missing_merge M L p n Payload0 H Hfresh)].
    unfold store_type_field; rewrite H3; csimpl; cancel; reflexivity. }
  sep_apply Hclose.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy51_correctness : typeinfer_rc_strategy51.
Proof.
  unfold typeinfer_rc_strategy51; intros n q p M L v; pre_process_default.
  subst q v.
  assert (Hfield : store_type_field M p n Payload1 = poly_store FET_ptr (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) (node_b n)).
  { unfold store_type_field; rewrite H3; reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload1) L) by assumption.
  assert (Hclose : (&( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand") # Ptr |-> (node_b n)) **
      store_world_missing M ((p,Payload1)::L) |-- store_world_missing M L).
  { eapply derivable1_trans; [|apply (store_world_missing_merge M L p n Payload1 H Hfresh)].
    unfold store_type_field; rewrite H3; csimpl; cancel; reflexivity. }
  sep_apply Hclose.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy52_correctness : typeinfer_rc_strategy52.
Proof.
  unfold typeinfer_rc_strategy52; intros n q p M L v; pre_process_default.
  subst q v.
  assert (Hfield : store_type_field M p n Payload0 = poly_store FET_int (&(p # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) (node_a n)).
  { unfold store_type_field; rewrite H3; reflexivity. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  assert (Hclose : (&( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name") # Int |-> (node_a n)) **
      store_world_missing M ((p,Payload0)::L) |-- store_world_missing M L).
  { eapply derivable1_trans; [|apply (store_world_missing_merge M L p n Payload0 H Hfresh)].
    unfold store_type_field; rewrite H3; csimpl; cancel; reflexivity. }
  sep_apply Hclose.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy53_correctness : typeinfer_rc_strategy53.
Proof.
  unfold typeinfer_rc_strategy53; intros n M p L; pre_process_default.
  assert (Htag : node_tag n = 0).
  { destruct H0 as [_ Hv]. specialize (Hv p n H).
  unfold payload_valid in Hv. lia. }
  unfold field_key.
  assert (Hfresh : ~ In (p,Payload0) L) by assumption.
  sep_apply (store_world_missing_split M L p n Payload0 H Hfresh).
  unfold store_type_field; rewrite Htag.
  entailer!.
  cancel (store_world_missing M ((p,Payload0)::L)).
  apply derivable1_sepcon_mono; [reflexivity|].
  Intros_r v. apply_sepcon_adjoint. entailer!; subst; csimpl; entailer!.
Qed.



Lemma typeinfer_rc_strategy54_correctness : typeinfer_rc_strategy54.
Proof.
  unfold typeinfer_rc_strategy54, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy55_correctness : typeinfer_rc_strategy55.
Proof.
  unfold typeinfer_rc_strategy55, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy56_correctness : typeinfer_rc_strategy56.
Proof.
  unfold typeinfer_rc_strategy56, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy57_correctness : typeinfer_rc_strategy57.
Proof.
  unfold typeinfer_rc_strategy57, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy58_correctness : typeinfer_rc_strategy58.
Proof.
  unfold typeinfer_rc_strategy58, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy59_correctness : typeinfer_rc_strategy59.
Proof.
  unfold typeinfer_rc_strategy59, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy60_correctness : typeinfer_rc_strategy60.
Proof.
  unfold typeinfer_rc_strategy60, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy61_correctness : typeinfer_rc_strategy61.
Proof.
  unfold typeinfer_rc_strategy61, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy62_correctness : typeinfer_rc_strategy62.
Proof.
  unfold typeinfer_rc_strategy62, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy63_correctness : typeinfer_rc_strategy63.
Proof.
  unfold typeinfer_rc_strategy63, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy64_correctness : typeinfer_rc_strategy64.
Proof.
  unfold typeinfer_rc_strategy64, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy65_correctness : typeinfer_rc_strategy65.
Proof.
  unfold typeinfer_rc_strategy65, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy66_correctness : typeinfer_rc_strategy66.
Proof.
  unfold typeinfer_rc_strategy66, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy67_correctness : typeinfer_rc_strategy67.
Proof.
  unfold typeinfer_rc_strategy67, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy68_correctness : typeinfer_rc_strategy68.
Proof.
  unfold typeinfer_rc_strategy68, field_lookup; pre_process_default.
  entailer!.
  Intros_r v. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy69_correctness : typeinfer_rc_strategy69.
Proof.
  unfold typeinfer_rc_strategy69, field_lookup; pre_process_default.
  entailer!.
  apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy70_correctness : typeinfer_rc_strategy70.
Proof.
  unfold typeinfer_rc_strategy70, field_lookup; pre_process_default.
  entailer!.
  Intros_r N. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy71_correctness : typeinfer_rc_strategy71.
Proof.
  unfold typeinfer_rc_strategy71, field_lookup; pre_process_default.
  entailer!.
  Intros_r N K. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy72_correctness : typeinfer_rc_strategy72.
Proof.
  unfold typeinfer_rc_strategy72, field_lookup; pre_process_default.
  entailer!.
  Intros_r v q. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy73_correctness : typeinfer_rc_strategy73.
Proof.
  unfold typeinfer_rc_strategy73, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy74_correctness : typeinfer_rc_strategy74.
Proof.
  unfold typeinfer_rc_strategy74, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy75_correctness : typeinfer_rc_strategy75.
Proof.
  unfold typeinfer_rc_strategy75, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy76_correctness : typeinfer_rc_strategy76.
Proof.
  unfold typeinfer_rc_strategy76, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy77_correctness : typeinfer_rc_strategy77.
Proof.
  unfold typeinfer_rc_strategy77, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy78_correctness : typeinfer_rc_strategy78.
Proof.
  unfold typeinfer_rc_strategy78, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy79_correctness : typeinfer_rc_strategy79.
Proof.
  unfold typeinfer_rc_strategy79, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy80_correctness : typeinfer_rc_strategy80.
Proof.
  unfold typeinfer_rc_strategy80, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy81_correctness : typeinfer_rc_strategy81.
Proof.
  unfold typeinfer_rc_strategy81, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy82_correctness : typeinfer_rc_strategy82.
Proof.
  unfold typeinfer_rc_strategy82, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy83_correctness : typeinfer_rc_strategy83.
Proof.
  unfold typeinfer_rc_strategy83, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy84_correctness : typeinfer_rc_strategy84.
Proof.
  unfold typeinfer_rc_strategy84, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy85_correctness : typeinfer_rc_strategy85.
Proof.
  unfold typeinfer_rc_strategy85, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy86_correctness : typeinfer_rc_strategy86.
Proof.
  unfold typeinfer_rc_strategy86, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy87_correctness : typeinfer_rc_strategy87.
Proof.
  unfold typeinfer_rc_strategy87, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy88_correctness : typeinfer_rc_strategy88.
Proof.
  unfold typeinfer_rc_strategy88, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy89_correctness : typeinfer_rc_strategy89.
Proof.
  unfold typeinfer_rc_strategy89, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy90_correctness : typeinfer_rc_strategy90.
Proof.
  unfold typeinfer_rc_strategy90, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy91_correctness : typeinfer_rc_strategy91.
Proof.
  unfold typeinfer_rc_strategy91, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy92_correctness : typeinfer_rc_strategy92.
Proof.
  unfold typeinfer_rc_strategy92, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy93_correctness : typeinfer_rc_strategy93.
Proof.
  unfold typeinfer_rc_strategy93, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy94_correctness : typeinfer_rc_strategy94.
Proof.
  unfold typeinfer_rc_strategy94, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy95_correctness : typeinfer_rc_strategy95.
Proof.
  unfold typeinfer_rc_strategy95, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy96_correctness : typeinfer_rc_strategy96.
Proof.
  unfold typeinfer_rc_strategy96, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy97_correctness : typeinfer_rc_strategy97.
Proof.
  unfold typeinfer_rc_strategy97, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy98_correctness : typeinfer_rc_strategy98.
Proof.
  unfold typeinfer_rc_strategy98, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy99_correctness : typeinfer_rc_strategy99.
Proof.
  unfold typeinfer_rc_strategy99, field_lookup, field_fresh, field_key; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy100_correctness : typeinfer_rc_strategy100.
Proof.
  unfold typeinfer_rc_strategy100, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy101_correctness : typeinfer_rc_strategy101.
Proof.
  unfold typeinfer_rc_strategy101, field_lookup.
  entailer!. Intros_r s L p. apply_sepcon_adjoint. entailer!.
Qed.

Lemma typeinfer_rc_strategy102_correctness : typeinfer_rc_strategy102.
Proof.
  unfold typeinfer_rc_strategy102, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

(* Explicit inequality matching avoids asking the arithmetic solver on both
   descent and ascent. The fallback only exposes an inequality already proved
   by the solver; it never assumes a lookup succeeded. *)
Lemma typeinfer_rc_strategy103_correctness : typeinfer_rc_strategy103.
Proof.
  unfold typeinfer_rc_strategy103, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

Lemma typeinfer_rc_strategy104_correctness : typeinfer_rc_strategy104.
Proof.
  unfold typeinfer_rc_strategy104, field_lookup, field_fresh, field_key;
  pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!;
    simpl in *; intuition congruence.
Qed.

Lemma typeinfer_rc_strategy105_correctness : typeinfer_rc_strategy105.
Proof.
  unfold typeinfer_rc_strategy105, field_lookup; pre_process_default;
  entailer!; try rewrite <- derivable1_wand_sepcon_adjoint; entailer!.
Qed.

