Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted path Zweight.
From MaxMinLib Require Import MaxMin Interface.
From ListLib Require Import Base.Inductive Base.Positional General.NoDup.

Import SetsNotation.

Local Open Scope sets.

Section EPATH.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

(* 基于原始Type Class destruct1n的导出定义valid_epath在list E上的归纳法 *)

(* epath: 存在一个P，使得P的edgeList等于它 *)
Definition valid_epath: 
  G -> V -> list E -> V -> Prop := 
  fun g u p v => exists P: P, 
    path_valid g P /\ 
    edge_in_path P = p /\ 
    head P = u /\ 
    tail P = v.


(* empty_path能构造出平凡的epath *)
Lemma valid_epath_empty: forall g v,
  valid_epath g v nil v.
Proof.
  intros.
  unfold valid_epath.
  exists (empty_path v).
  assert (path_valid g (empty_path v)) by (apply empty_path_valid).
  split; [auto|].
  split; [|split]; auto.
  - apply (empty_path_edge g).
  - apply Some_inversion. erewrite head_valid; eauto. 
    rewrite empty_path_vertex. simpl. auto.
  - apply Some_inversion. erewrite tail_valid; eauto. 
    rewrite empty_path_vertex. simpl. auto.
Qed.

(* nil的epath对应 (empty_path v) *)
Lemma valid_epath_nil_inv:
  forall g u v,
  valid_epath g u nil v ->
  u = v.
Proof.
  intros.
  destruct H as [path_obj [H_pval [H_edges [H_hd H_tl]]]].
  apply Some_injection in H_hd, H_tl.
  erewrite head_valid in H_hd; eauto.
  erewrite tail_valid in H_tl; eauto.
  pose proof (vpath_iff_epath g path_obj H_pval) as [Hlen _].
  rewrite H_edges in Hlen. simpl in Hlen.
  destruct (vertex_in_path path_obj) as [| x [| y l]].
  - simpl in Hlen; lia.
  - simpl in H_hd; injection H_hd as Hu; subst.
    simpl in H_tl; injection H_tl as Hv; subst.
    reflexivity.
  - simpl in Hlen; lia.
Qed.

(* single_path能构造出单步的epath *)
Lemma valid_epath_single: forall g u v e,
  step_aux g e u v ->
  valid_epath g u (e :: nil) v.
Proof.
  intros.
  unfold valid_epath. 
  assert (Hvalid: path_valid g (single_path u v e)) by (apply single_path_valid; auto).
  exists (single_path u v e). split; [auto|].
  split; [|split]; auto.
  - rewrite single_path_edge. reflexivity.
  - apply Some_inversion. erewrite head_valid; eauto. rewrite single_path_vertex; simpl; auto.
  - apply Some_inversion. erewrite tail_valid; eauto. rewrite single_path_vertex; simpl; auto.
Qed.

(* epath的singleton对应一个step关系 *)
Lemma valid_epath_single_inv:
  forall g u v e,
  valid_epath g u (e :: nil) v ->
  step_aux g e u v.
Proof.
  intros. 
  destruct H as [p [Hp [Hedge [Hhd Htl]]]]. 
  pose proof (vpath_iff_epath g p Hp) as [Hlen Hstep]. 
  rewrite Hedge in Hlen; simpl in Hlen. 
  apply Some_injection in Hhd. erewrite head_valid in Hhd; eauto. 
  apply Some_injection in Htl. erewrite tail_valid in Htl; eauto. 
  rewrite <- nth_error_O in Hhd. 
  unfold tl_error in Htl; rewrite Hlen in Htl.
  pose proof Hstep 0%nat u v e ltac:(rewrite Hedge; simpl; lia) ltac:(rewrite Hedge; simpl; auto) Hhd Htl.
  apply H.
Qed.



(* epath的++也是epath *)
Lemma valid_epath_app:
  forall g u p1 v p2 w,
    valid_epath g u p1 v ->
    valid_epath g v p2 w ->
    valid_epath g u (p1 ++ p2) w.
Proof.
  intros.
  destruct H as [P1 [Hp1 [Hedge1 [Hhd1 Htl1]]]].
  destruct H0 as [P2 [Hp2 [Hedge2 [Hhd2 Htl2]]]]. 

  apply Some_injection in Hhd1, Hhd2, Htl1, Htl2.
  erewrite head_valid in Hhd1, Hhd2; eauto.
  erewrite tail_valid in Htl1, Htl2; eauto.
  
  exists (concat_path P1 P2).
  
  assert (Hconnect: tail P1 = head P2).
  { 
    apply Some_inversion.
    erewrite tail_valid by eauto.
    erewrite head_valid by eauto.
    rewrite Htl1, Hhd2. reflexivity. 
  } 
  assert (Hvalid: path_valid g (concat_path P1 P2)) by (apply concat_path_valid; auto).
  split; [|split; [|split]]; auto.
  - rewrite concat_path_edge. rewrite Hedge1, Hedge2. reflexivity.
  - apply Some_inversion. erewrite head_valid; eauto. 
    rewrite concat_path_vertex.
    destruct (vertex_in_path P1); [discriminate|simpl; auto].
  - apply Some_inversion. erewrite tail_valid; eauto. 
    rewrite concat_path_vertex.
    destruct (vertex_in_path P2); [discriminate|simpl in *; auto].
    destruct (list_snoc_destruct l); [subst; simpl in *|].
    * unfold tl_error in Htl2; simpl in Htl2. 
      inversion Hhd2 ; inversion Htl2; subst. 
      rewrite app_nil_r; auto. 
    * destruct H as [? []]; subst. 
      rewrite! app_assoc.
      rewrite tl_error_last.
      rewrite app_comm_cons in Htl2.
      rewrite tl_error_last in Htl2.
      auto. 
Qed.

(* cons构造的epath以分解为一个单步和一个epath *)
Lemma valid_epath_cons_inv:
  forall g u e p w,
  valid_epath g u (e :: p) w ->
  exists v, step_aux g e u v /\ valid_epath g v p w.
Proof. 
  intros.
  destruct H as [p0 [Hp [Hedge [Hhd Htl]]]]. 
  apply Some_injection in Hhd, Htl.
  erewrite head_valid in Hhd; eauto.
  erewrite tail_valid in Htl; eauto.
  pose proof (destruct_1n_spec g p0 Hp).
  destruct (destruct_1n_path g p0 Hp) eqn: ?;
  unfold path_cons_spec in *.
  - (* Base Case: P implies empty edges *)
    subst. rewrite (empty_path_edge g) in Hedge. discriminate.
  - (* Step Case *)
    destruct H as [Hp' [Hhd' [Hstep Heq]]].
    subst p0.
    rewrite concat_path_edge in Hedge.
    rewrite single_path_edge in Hedge.
    simpl in Hedge. injection Hedge as He Hp_eq. subst.
    
    rewrite concat_path_vertex in Hhd.
    rewrite single_path_vertex in Hhd.
    simpl in Hhd. injection Hhd as Hu. subst u0.

    exists (head p1). split; auto.
    
    exists p1. split; [|split; [|split]]; auto. 
    apply Some_inversion. erewrite tail_valid; eauto.
    rewrite concat_path_vertex in Htl.
    rewrite single_path_vertex in Htl.
    destruct (vertex_in_path p1) eqn:Hvpath.
    * eapply path_valid_vertex_not_nil in Hp'; congruence.
    * simpl in Htl. 
      destruct (list_snoc_destruct l); [subst; simpl in *|].
      + unfold tl_error in Htl; simpl in Htl.
        unfold tl_error; simpl.
        erewrite head_valid in Htl; eauto. 
        rewrite Hvpath in Htl; simpl in Htl. 
        auto.
      + destruct H as [? []]; subst. 
        rewrite app_comm_cons.
        rewrite tl_error_last.
        simpl in Htl. 
        rewrite! app_comm_cons in Htl.
        rewrite tl_error_last in Htl.
        auto.
Qed.

(* ++构成的epath能够被拆散 *)
Lemma valid_epath_app_inv:
  forall g u p1 p2 w,
  valid_epath g u (p1 ++ p2) w ->
  exists v, valid_epath g u p1 v /\ valid_epath g v p2 w.
Proof.
  intros g u p1.
  revert u.
  induction p1; intros u p2 w H.
  - simpl in H.
    exists u; split; auto.
    apply valid_epath_empty.
  - (* p1 = a :: p1 *)
    rewrite <- app_comm_cons in H.
    apply valid_epath_cons_inv in H.
    destruct H as [v' [Hstep Hvalid_rest]].
    apply IHp1 in Hvalid_rest.
    destruct Hvalid_rest as [target [Hsub1 Hsub2]].
    exists target. split; auto.
    apply (valid_epath_app g u (a::nil) v' p1 target); auto.
    apply valid_epath_single; auto.
Qed.

(* epath的单步cons也是epath *)
Lemma valid_epath_cons:  
  forall g u e p v w,
  step_aux g e u v ->
  valid_epath g v p w ->
  valid_epath g u (e :: p) w.
Proof.
  intros.
  replace (e :: p) with ((e :: nil) ++ p) by auto.
  eapply valid_epath_app; [| apply H0].
  apply valid_epath_single; auto.
Qed.

(* epath的尾部接上单步也是epath *)
Lemma valid_epath_snoc:
  forall g u p v w e,
  valid_epath g u p v ->
  step_aux g e v w ->
  valid_epath g u (p ++ e :: nil) w.
Proof.
  intros.
  eapply valid_epath_app.
  - apply H.
  - apply valid_epath_single; auto.
Qed.

(* epath能够从尾部拆分 *)
Lemma valid_epath_snoc_inv:
  forall g u p e w,
  valid_epath g u (p ++ e :: nil) w ->
  exists v, valid_epath g u p v /\ step_aux g e v w.
Proof.
  intros.
  apply valid_epath_app_inv in H.
  destruct H as [v [Hpre Hsuf]].
  apply valid_epath_single_inv in Hsuf.
  exists v. auto.
Qed.

(* epath上对list E的1n归纳法则 *)
Lemma valid_epath_ind_1n:
  forall g (X : V -> list E -> V -> Prop)
  (Hbase: forall v, X v nil v)
  (Hind: forall u v e p w,
    step_aux g e u v -> 
    valid_epath g v p w -> 
    X v p w ->
    X u (e :: p) w),
  forall u p v, valid_epath g u p v -> X u p v.
Proof.
  intros g X Hbase Hind u p v Hvalid.
  revert u v Hvalid.
  induction p as [|e p IH]; intros u v Hvalid.
  - (* Base Case: nil *)
    apply valid_epath_nil_inv in Hvalid. subst.
    apply Hbase.
  - (* Step Case: e :: p *)
    apply valid_epath_cons_inv in Hvalid.
    destruct Hvalid as [v_next [Hstep Hvalid_rest]].
    apply Hind with (v := v_next); auto.
Qed.

(* epath 上对 list E 的 n1 归纳法则 *)
Lemma valid_epath_ind_n1:
  forall g (X : V -> list E -> V -> Prop)
  (Hbase: forall v, X v nil v)
  (Hind: forall u p v w e,
    valid_epath g u p v -> 
    X u p v ->
    step_aux g e v w -> 
    X u (p ++ e :: nil) w),
  forall u p v, valid_epath g u p v -> X u p v.
Proof.
  intros g X Hbase Hind u p v H.
  revert u v H.
  induction p using rev_ind; intros u v H.
  - apply valid_epath_nil_inv in H. subst.
    apply Hbase.
  - apply valid_epath_snoc_inv in H.
    destruct H as [v_mid [H_prefix H_step]].
    apply Hind with (v := v_mid).
    + exact H_prefix.
    + apply IHp with (v := v_mid).
      exact H_prefix.
    + exact H_step.
Qed.

(* epath能够被n1分解，即平凡的单步或epath++单步 *)
Lemma valid_epath_inv_n1:
  forall g u p v,
  valid_epath g u p v ->
  (u = v /\ p = nil) \/
  (exists p' w e, p = p' ++ e :: nil /\ valid_epath g u p' w /\ step_aux g e w v).
Proof.
  intros.
  destruct p as [| x l] using rev_ind.
  - left. split; [eapply valid_epath_nil_inv; eauto | reflexivity].
  - right. apply valid_epath_snoc_inv in H as [w [Hpre Hstep]].
    exists l, w, x. auto.
Qed.

(* epath能够被1n分解，即平凡的单步或单步++epath *)
Lemma valid_epath_inv_1n: 
  forall g u p v,
  valid_epath g u p v ->
  (u = v /\ p = nil) \/
  (exists e w p', p = e :: p' /\ step_aux g e u w /\ valid_epath g w p' v).
Proof.
  intros.
  destruct p as [|e p].
  - apply valid_epath_nil_inv in H; subst; auto.
  - apply valid_epath_cons_inv in H as [w [Hstep Hvalid_rest]]. 
    right; exists e; exists w; exists p; split; [|split]; auto.
Qed.

(* epath能够被转换为reachable *)
Lemma valid_epath_reachable:
  forall g u p v,
  valid_epath g u p v ->
  reachable g u v.
Proof.
  intros.
  revert u p v H.
  apply valid_epath_ind_1n.
  - (* Base: nil *)
    intros. reflexivity.
  - (* Step: e :: p *)
    intros.
    eapply step_reachable_reachable.
    exists e. eauto. auto.
Qed.

Lemma valid_epath_reachable_without:
  forall g u v p e,
    valid_epath g u p v ->
    ~ In e p ->
    reachable_without g e u v.
Proof.
  intros g u v p.
  revert u v.
  induction p as [|a p IHp]; intros u v e Hvalid Hnotin.
  - apply valid_epath_nil_inv in Hvalid.
    subst; reflexivity.
  - apply valid_epath_cons_inv in Hvalid as [w [Hstep Hrest]].
    unfold reachable_without.
    transitivity_1n w.
    + exists a; split; auto.
      intro Heq; apply Hnotin; subst; simpl; auto.
    + apply (IHp w v e); auto.
      intro Hin; apply Hnotin; simpl; auto.
Qed.

(* reachable能够被转换为epath *)
Lemma reachable_valid_epath:
  forall g u v,
  reachable g u v ->
  exists p, valid_epath g u p v.
Proof.
  intros.
  unfold reachable in H.
  induction_1n H.
  - exists nil. apply valid_epath_empty.
  - destruct IHrt as [p Hvalid].
    destruct H0 as [e Hstep].
    exists (e :: p).
    eapply valid_epath_cons; eauto.
Qed.

Lemma reachable_without_valid_epath: 
  forall g u v e, 
  reachable_without g e u v -> 
  exists p, valid_epath g u p v /\ ~ In e p.
Proof. 
  intros. 
  unfold reachable_without in H.
  induction_1n H.
  - exists nil. split; [apply valid_epath_empty|simpl; auto]. 
  - destruct IHrt as [p [Hvalid Hnot_in]]. 
    destruct H0 as [e0 [Hstep Hne]].
    exists (e0 :: p); split.
    + eapply valid_epath_cons; eauto.
    + simpl; unfold not; intros []; auto.
Qed.


Theorem valid_epath_rev
  {undirected:UndirectedGraph G V E}:
  forall g u p v,
    valid_epath g u p v ->
    valid_epath g v (rev p) u.
Proof.
  intros g u p.
  induction p using rev_ind; intros v Hvalid.
  - simpl in *.
    apply valid_epath_nil_inv in Hvalid.
    subst v.
    apply valid_epath_empty.
  - rewrite rev_unit.
    apply valid_epath_snoc_inv in Hvalid.
    destruct Hvalid as [w [Hpre Hstep]].
    specialize (IHp _ Hpre).
    eapply valid_epath_cons; eauto.
    eapply step_sym; eauto.
Qed.

Theorem valid_epath_cross:
  forall P g u v p,
    P u -> ~ P v ->
    valid_epath g u p v -> 
    exists x y a, P x /\ ~ P y /\ step_aux g a x y /\ In a p.
Proof.
  intros Q g u v p Hu Hv Hvalid.
  revert u Hu Hvalid.
  induction p as [|a p IH]; intros x Hu Hvalid.
  - apply valid_epath_nil_inv in Hvalid; subst; contradiction.
  - apply valid_epath_cons_inv in Hvalid as [z [Hstep Hrest]].
    destruct (classic (Q z)) as [Hz | Hz].
    + destruct (IH z Hz Hrest) as [x' [y' [b [Hx' [Hy' [Hstep' Hin']]]]]].
      exists x', y', b; repeat split; auto.
      simpl; right; auto.
    + exists x, z, a; repeat split; auto.
      simpl; left; auto. 
Qed.

(* epath上的简单路径：不经过重复边 *)
Definition is_simple_epath (g: G) (u: V) (p: list E) (v: V): Prop :=
  valid_epath g u p v /\ NoDup p.

(* 移除epath中的环 *)
(* 需要边的某种唯一性；有向图的边唯一性强于无向图的边唯一性，所有我们只证明后者 *)
Lemma valid_epath_shorten_cycle
  (g: G)
  {step_aux_unique_undirected: forall e x1 y1 x2 y2, step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1)}: 
  forall u v l1 e l2 l3,
  valid_epath g u (l1 ++ e :: l2 ++ e :: l3) v ->
  exists q, valid_epath g u q v /\ 
  length q < length (l1 ++ e :: l2 ++ e :: l3) /\ 
  forall x, In x q -> In x (l1 ++ e :: l2 ++ e :: l3).
Proof.
  intros u v l1 e l2 l3 H.
  apply valid_epath_app_inv in H.
  destruct H as [u_mid [H_path_l1 H_rest1]].
  apply valid_epath_cons_inv in H_rest1.
  destruct H_rest1 as [v_mid [H_step1 H_rest2]].
  apply valid_epath_app_inv in H_rest2.
  destruct H_rest2 as [u_mid2 [H_path_l2 H_tail]].
  apply valid_epath_cons_inv in H_tail.
  destruct H_tail as [v_mid2 [H_step2 H_path_l3]].
  pose proof (step_aux_unique_undirected e u_mid v_mid u_mid2 v_mid2 H_step1 H_step2) 
  as [[]|[]]; subst.
  - exists (l1 ++ e :: l3).
    split; [|split].
    + eapply valid_epath_app; eauto.
      eapply valid_epath_cons; eauto.
    + rewrite !length_app; simpl.
      rewrite !length_app; simpl. lia. 
    + intros x Hx. 
      rewrite in_app_iff in *; simpl in *; 
      rewrite in_app_iff in *; simpl in *. 
      tauto. 
  - exists (l1 ++ l3).
    split; [|split].
    + eapply valid_epath_app; eauto.
    + rewrite !length_app; simpl. 
      rewrite !length_app; simpl. lia.
    + intros x Hx. 
      rewrite in_app_iff in *; simpl in *; 
      rewrite in_app_iff in *; simpl in *. 
      tauto. 
Qed.

(* 任意两点之间的epath能够被转换为简单的epath *)
(* 前提：给出无向图或有向图的step_aux的type class *)
(* 这也提示出step_aux或许处于一个不正确的位置 *)
(* 一个由起点和边能确定终点的前提是不够的。因为我们在epath上面不能获取起点相同的条件。 *)
Theorem valid_epath_simple 
  (g: G)
  {step_aux_unique_undirected: forall e x1 y1 x2 y2, step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1)}:
  forall u p v,
  valid_epath g u p v ->
  exists q, is_simple_epath g u q v.
Proof.
  intros u p v H_valid.
  remember (length p) as n.
  revert u p v H_valid Heqn.
  induction n using lt_wf_ind; intros u p v H_valid Heqn.
  destruct (classic (NoDup p)).
  - exists p. split; auto.
  - apply Nodup_exists_repetition in H0.
    destruct H0 as [e [l1 [l2 [l3 H_eq]]]].
    subst p.
    pose proof (@valid_epath_shorten_cycle g step_aux_unique_undirected u v l1 e l2 l3 H_valid) 
    as [q [H_valid_q H_len_q]].
    apply (H (length q)) in H_valid_q; auto.
    lia.
Qed.

(* gvalid需要再处理一下 *)
Theorem valid_epath_simple_directed 
  (g: G)
  {undirected: StepUniqueUndirected G V E}
  {g_valid: gvalid g}:
  forall u p v,
  valid_epath g u p v ->
  exists q, is_simple_epath g u q v.
Proof.
  intros u p v H_valid. 
  eapply valid_epath_simple; eauto. 
  intros. 
  eapply step_aux_unique_undirected in H. 
  3:{ apply H0. }
  destruct H as [[]|[]]; subst; auto. auto. 
Qed.


Lemma valid_epath_simple_Forall 
  (g: G)
  {step_aux_unique_undirected: forall e x1 y1 x2 y2, step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1)}:
  forall eset u p v,
    valid_epath g u p v ->
    Forall eset p ->
    exists q, is_simple_epath g u q v /\ Forall eset q.
Proof.
  intros eset u p v H_valid Hfor.
  remember (length p) as n.
  revert u p v H_valid Hfor Heqn.
  induction n using lt_wf_ind; intros u p v H_valid Hfor Heqn.
  destruct (classic (NoDup p)).
  - exists p; split; [split|]; auto.
  - apply Nodup_exists_repetition in H0.
    destruct H0 as [e [l1 [l2 [l3 H_eq]]]].
    subst p. 
    eapply valid_epath_shorten_cycle in H_valid as [q [Hqpath [Hqlt Hsub]]]; eauto.
    specialize (H (length q) ltac:(lia) u q v Hqpath). 
    apply H; auto.
    rewrite Forall_forall in *; auto.
Qed.


(* vset就等于path去掉首尾后的所有点的集合 *)
Definition is_epath_through_exactly_vset 
  (g: G) (u: V) (p: list E) (v: V) (vset: V -> Prop): Prop :=
  valid_epath g u p v /\ 
  forall x, x ∈ vset <-> 
  exists p1 p2, 
    p1 <> nil /\ (* 去掉头 *)
    p2 <> nil /\ (* 去掉尾 *) 
    valid_epath g u p1 x /\ 
    valid_epath g x p2 v /\ 
    p1 ++ p2 = p . 

(* 路径的中间节点都在vset中 *)
Definition is_epath_through_vset
  (g: G) (u: V) (p: list E) (v: V) (S: V -> Prop) : Prop :=
  valid_epath g u p v /\ 
  forall (p1 p2: list E) (x: V),
    p1 <> nil ->
    p2 <> nil ->
    p = p1 ++ p2 ->
    valid_epath g u p1 x ->
    x ∈ S.


#[export] Instance is_epath_through_vset_Proper:
  Proper (eq ==> eq ==> eq ==> eq ==> Sets.equiv ==> iff) is_epath_through_vset.
Proof.
  intros g1 g2 Heq_g u1 u2 Heq_u p1 p2 Heq_p v1 v2 Heq_v S1 S2 Heq_S; 
  subst; split; intros. 
  - destruct H as [Hvalid Hprop].
    split; [auto|]; intros. 
    rewrite <- Heq_S. 
    eapply (Hprop p1 p0); eauto. 
  - destruct H as [Hvalid Hprop].
    split; [auto|]; intros. 
    rewrite Heq_S. 
    eapply (Hprop p1 p0); eauto.
Qed. 


(* 空路径总是满足任意 S *)
Lemma is_epath_through_vset_nil: 
  forall g u S,
    is_epath_through_vset g u nil u S.
Proof.
  intros. split.
  - apply valid_epath_empty.
  - intros. destruct p1; simpl in *; try congruence.
Qed.

(* 单条边总是满足任意 S *)
Lemma is_epath_through_vset_single: 
  forall g u v e S,
    step_aux g e u v ->
    is_epath_through_vset g u (e :: nil) v S.
Proof.
  intros. split.
  - apply valid_epath_single; auto.
  - intros p1 p2 x Hp1 Hp2 Hp Hvalid. 
    destruct p1; [congruence|]. 
    inversion Hp; subst. 
    symmetry in H2; apply app_eq_nil in H2 as []; subst. 
    congruence. 
Qed. 

Lemma is_epath_through_vset_subset:
  forall g u p v S1 S2,
    is_epath_through_vset g u p v S1 ->
    S1 ⊆ S2 ->
    is_epath_through_vset g u p v S2.
Proof.
  intros g u p v S1 S2 [Hvalid Hprop] Hsubset.
  split; [auto|].
  intros p1 p2 x Hp1 Hp2 Heq Hvalid1.
  rewrite <- Hsubset. 
  eapply (Hprop p1 p2); eauto.
Qed.

(* 相同起点同一路径的终点是唯一的；这一性质同时存在于有向图和无向图之中 *)
Context {step_aux_unique: StepUniqueDirected G V E}
        {g: G}
        {g_valid: gvalid g}.

Lemma step_aux_unique_end: forall u e v1 v2, 
  step_aux g e u v1 -> step_aux g e u v2 -> v1 = v2.
Proof. intros; eapply step_aux_unique in H as []; eauto. Qed. 

Lemma step_aux_unique_start: forall u1 u2 e v, 
  step_aux g e u1 v -> step_aux g e u2 v -> u1 = u2.
Proof. intros; eapply step_aux_unique in H as []; eauto. Qed.

Theorem valid_epath_unique_end:
  forall u p v1 v2, 
    valid_epath g u p v1 -> 
    valid_epath g u p v2 -> 
    v1 = v2.
Proof.
  intros. 
  revert u v1 v2 H H0. 
  induction p. 
  - intros. 
    apply valid_epath_nil_inv in H, H0. 
    subst; reflexivity. 
  - intros. 
    apply valid_epath_cons_inv in H, H0. 
    destruct H as [v [Hstep Hvalid]]. 
    destruct H0 as [v' [Hstep' Hvalid']]. 
    assert (v = v') by (eapply step_aux_unique_end; eauto); subst v'.
    eapply IHp; eauto.
Qed. 

Theorem valid_epath_unique_start:
  forall u1 u2 p v, 
    valid_epath g u1 p v -> 
    valid_epath g u2 p v -> 
    u1 = u2.
Proof.
  intros. 
  revert u1 u2 v H H0.
  induction p using rev_ind.
  - intros.
    apply valid_epath_nil_inv in H, H0.
    subst; reflexivity.
  - intros.
    apply valid_epath_snoc_inv in H, H0.
    destruct H as [v1 [Hvalid1 Hstep1]].
    destruct H0 as [v2 [Hvalid2 Hstep2]].
    assert (v1 = v2) by (eapply step_aux_unique_start; eauto); subst v2.
    eapply IHp; eauto.
Qed.

(* 如果中点k在集合S里面，则允许经过的集合不变 *)
Theorem is_epath_through_vset_app: 
  forall u p1 m p2 v S,
    is_epath_through_vset g u p1 m S ->
    is_epath_through_vset g m p2 v S ->
    m ∈ S -> 
    is_epath_through_vset g u (p1 ++ p2) v S.
Proof.
  intros u p1 m p2 v S 
  [Hvalid1 Hp1] [Hvalid2 Hp2] Hm; split.
  - eapply valid_epath_app; eauto.
  - intros q1 q2 x Hq1 Hq2 Hq Hvalid. 
    apply app_eq_app in Hq as [[n [Hpre Hpost]]|[n [Hpost Hpre]]].
    + assert (Hn: n = nil \/ n <> nil) by tauto; destruct Hn. 
      * subst. rewrite app_nil_r in Hvalid1. 
        assert (x = m) by (eapply valid_epath_unique_end; eauto); subst x.
        subst; auto. 
      * eapply (Hp1 q1 n); eauto.
    + assert (Hn: n = nil \/ n <> nil) by tauto; destruct Hn.
      * subst. rewrite app_nil_r in Hvalid.
        assert (x = m) by (eapply valid_epath_unique_end; eauto); subst x.
        subst; auto.
      * subst; eapply (Hp2 n q2); eauto. 
        eapply valid_epath_app_inv in Hvalid as [? [? ?]]. 
        assert (x0 = m) by (eapply valid_epath_unique_end; eauto); subst x0.
        auto.
Qed. 

(* 如果不考虑中点k的位置，可以直接把它加到允许通过的集合里面去 *)
Theorem is_epath_through_vset_union: 
  forall u p1 m p2 v S,
    is_epath_through_vset g u p1 m S ->
    is_epath_through_vset g m p2 v S -> 
    is_epath_through_vset g u (p1 ++ p2) v (S ∪ [m]).
Proof.
  intros u p1 m p2 v S 
  [Hvalid1 Hp1] [Hvalid2 Hp2]; split.
  - eapply valid_epath_app; eauto.
  - intros q1 q2 x Hq1 Hq2 Hq Hvalid.
    apply app_eq_app in Hq as [[n [Hpre Hpost]]|[n [Hpost Hpre]]].
    + assert (Hn: n = nil \/ n <> nil) by tauto; destruct Hn.
      * subst. rewrite app_nil_r in Hvalid1.
        assert (x = m) by (eapply valid_epath_unique_end; eauto); subst x.
        right; reflexivity.
      * left; eapply (Hp1 q1 n); eauto.
    + assert (Hn: n = nil \/ n <> nil) by tauto; destruct Hn.
      * subst. rewrite app_nil_r in Hvalid.
        assert (x = m) by (eapply valid_epath_unique_end; eauto); subst x. 
        right; reflexivity. 
      * left; subst; eapply (Hp2 n q2); eauto. 
        eapply valid_epath_app_inv in Hvalid as [? [? ?]]. 
        assert (x0 = m) by (eapply valid_epath_unique_end; eauto); subst x0.
        auto.
Qed.

Lemma is_epath_through_vset_cons:
  forall u e w p v S,
    is_epath_through_vset g w p v S ->  
    w ∈ S -> 
    step_aux g e u w ->
    is_epath_through_vset g u (e :: p) v S.
Proof. 
  intros. 
  apply is_epath_through_vset_single with (S:=S) in H1.  
  pose proof is_epath_through_vset_app _ _ _ _ _ _ H1 H H0. 
  rewrite <- app_comm_cons in H2. 
  auto. 
Qed.

Theorem is_epath_through_vset_split: 
  forall u p v S (k: V),
  is_epath_through_vset g u p v (S ∪ [k]) ->
  is_epath_through_vset g u p v S \/ 
  exists p_pre p_mid p_suf,
    is_epath_through_vset g u p_pre k S /\ 
    is_epath_through_vset g k p_suf v S /\ 
    is_epath_through_vset g k p_mid k (S ∪ [k]) /\ 
    p = p_pre ++ p_mid ++ p_suf. 
Proof. 
  intros u p; revert u. 
  induction p as [|e p IHp]; intros u v S k H. 
  1:{ left. destruct H as [? _]. 
      apply valid_epath_nil_inv in H; subst. 
      apply is_epath_through_vset_nil. }
  destruct H as [Hvalid Hprop].
  apply valid_epath_cons_inv in Hvalid as [w [Hstep Hvalid_rest]].
  destruct p as [| e' q]. 
  1:{ left. apply is_epath_through_vset_single; auto. 
      apply valid_epath_nil_inv in Hvalid_rest; subst w; auto. }

  assert (H_w_in_union: w ∈ (S ∪ [k])) by
  ( eapply Hprop with (p1 := e :: nil) (p2 := e' :: q); 
    try discriminate; auto; 
    apply valid_epath_single; auto).

  assert (H_tail_prop: is_epath_through_vset g w (e' :: q) v (S ∪ [k])). {
    split; [auto|].
    intros p1 p2 x Hp1 Hp2 Heq Hsub.
    eapply Hprop with (p1 := e :: p1) (p2 := p2); try discriminate; auto.
    + simpl; rewrite Heq; auto.
    + eapply valid_epath_cons; eauto. }

  specialize (IHp w v S k H_tail_prop).
  
  destruct IHp as [H_tail_S | [p_pre_tail [p_mid_tail [p_suf_tail [H_tail_pre [H_tail_suf [H_tail_mid Heq]]]]]]].
      
  - destruct H_w_in_union. 
    * left; eapply is_epath_through_vset_cons; eauto. 
    * right; sets_unfold in H; subst. 
      exists (e :: nil), nil, (e' :: q); split; [| split; [| split]]; auto.
      + apply is_epath_through_vset_single; auto.
      + apply is_epath_through_vset_nil.

  - destruct H_w_in_union. 
    * right; exists (e :: p_pre_tail), p_mid_tail, p_suf_tail; split; [| split; [| split]]; auto.
      eapply is_epath_through_vset_cons; eauto. 
      rewrite Heq; rewrite app_comm_cons; reflexivity.
    * right; sets_unfold in H; subst. 
      exists (e :: nil), (p_pre_tail ++ p_mid_tail), p_suf_tail; split; [| split; [| split]]; auto.
      + apply is_epath_through_vset_single; auto. 
      + eapply is_epath_through_vset_app; eauto;
        [|right; reflexivity].
        eapply is_epath_through_vset_subset; eauto; left; auto.
      + rewrite Heq. rewrite !app_assoc. rewrite app_comm_cons. 
        reflexivity. 
Qed.


Theorem is_epath_through_vset_greedy_cut:
  forall u p v S,
    valid_epath g u p v ->
    ~ v ∈ S ->
    exists x p1 p2,
      is_epath_through_vset g u p1 x S /\
      ~ x ∈ S /\
      valid_epath g x p2 v /\
      p = p1 ++ p2.
Proof. 
  intros u p; revert u. 
  induction p as [|e p IHp]; intros u v S Hvalid Hv.
  1: { apply valid_epath_nil_inv in Hvalid; subst. 
    exists v, nil, nil; split; [|split; [|split]]; auto. 
    apply is_epath_through_vset_nil. 
    apply valid_epath_empty. } 
  apply valid_epath_cons_inv in Hvalid as [w [Hstep Hvalid_rest]].
  specialize (IHp w v S Hvalid_rest Hv).
  destruct IHp as [x [p1 [p2 [Hp1 [Hp2 [Hp Heq]]]]]].
  destruct (classic (w ∈ S)) as [Hw | Hwn]. 
  2: { 
    exists w, (e :: nil), p; split; [|split; [|split]]; auto. 
    apply is_epath_through_vset_single; auto. } 
  exists x, (e :: p1), p2; split; [|split; [|split]]; auto.
  * eapply (is_epath_through_vset_cons u e w p1 x); eauto. 
  * rewrite Heq; auto. 
Qed.  

Theorem is_epath_through_vset_app_inv: 
  forall u p1 p2 v S, 
    is_epath_through_vset g u (p1 ++ p2) v S -> 
    p1 <> nil -> 
    p2 <> nil ->
      exists x, x ∈ S /\ is_epath_through_vset g u p1 x S /\ is_epath_through_vset g x p2 v S.
Proof.
  intros u p1 p2 v S H Hp1 Hp2.
  destruct H. 
  apply valid_epath_app_inv in H as [k []]. 
  exists k; split; [|split]. 
  - eapply (H0 p1 p2); eauto. 
  - split; auto. 
    intros. 
    pose proof H0 p0 (p3 ++ p2) x H2 
    ltac:(destruct p3; [simpl; auto|symmetry; apply nil_cons])
    ltac:(rewrite H4; rewrite app_assoc; auto) H5; auto.
  - split; auto. 
    intros. 
    pose proof H0 (p1 ++ p0) p3 x
    ltac:(destruct p1; [simpl; auto|symmetry; apply nil_cons]) H3
    ltac:(rewrite H4; rewrite app_assoc; auto)
    ltac:(eapply valid_epath_app; eauto); auto.
Qed.


(* 我们也可以基于epath进行最短路径的定义和证明。 *)

Context {ew: EdgeWeight G E}. 

Local Open Scope Z.

Definition epath_weight (g: G) (p: list E): option Z :=
  fold_right Z_op_plus (Some 0) (map (weight g) p). 

Theorem epath_weight_nil: 
  epath_weight g nil = Some 0.
Proof. unfold epath_weight; simpl; auto. Qed.

Theorem epath_weight_single: 
  forall e, epath_weight g (e :: nil) = weight g e.
Proof.
  intros. unfold epath_weight; simpl. 
  rewrite Z_op_plus_O_r. reflexivity. 
Qed.

Theorem epath_weight_cons:
  forall g e p,
    epath_weight g (e :: p) = Z_op_plus (weight g e) (epath_weight g p).
Proof.
  intros.
  unfold epath_weight.
  rewrite map_cons.
  rewrite Zlist_sum_cons.
  reflexivity.
Qed.

Theorem epath_weight_app_assoc:
  forall g p1 p2, 
    epath_weight g (p1 ++ p2) = Z_op_plus (epath_weight g p1) (epath_weight g p2).
Proof.
  intros.
  unfold epath_weight.
  rewrite map_app.
  rewrite Zlist_sum_app.
  reflexivity.
Qed.

Definition min_object_weight_epath (g: G) (u: V) (v: V) (p: list E): Prop :=
  min_object_of_subset Z_op_le (fun p => valid_epath g u p v) (epath_weight g) p. 

Definition min_value_weight_epath (g: G) (u: V) (v: V) (z: option Z): Prop :=
  min_value_of_subset_with_default Z_op_le (fun p => valid_epath g u p v) (epath_weight g) None z. 

Definition min_object_weight_epath_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (p: list E): Prop :=
  min_object_of_subset Z_op_le (fun p => is_epath_through_vset g u p v vset) (epath_weight g) p. 

Definition min_value_weight_epath_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (z: option Z): Prop :=
  min_value_of_subset_with_default Z_op_le (fun p => is_epath_through_vset g u p v vset) (epath_weight g) None z.     

#[export] Instance min_value_weight_epath_in_vset_Proper:
  Proper (eq ==> eq ==> eq ==> Sets.equiv ==> eq ==> iff) min_value_weight_epath_in_vset.
Proof.
  intros g1 g2 Heq_g u1 u2 Heq_u v1 v2 Heq_v vset1 vset2 Heq_vset z1 z2 Heq_z; 
  subst; split; intros.
  - destruct H as [[? _]|[]]; [left|right]. 
    * split; [|destruct z2; simpl; auto]. 
      destruct H as [p [[Hvalid Hmin] Hpeq]]. 
      exists p; split; auto. 
      split. 
      + sets_unfold. 
        rewrite <- Heq_vset; auto. 
      + intros q Hq. 
        apply Hmin. 
        sets_unfold. 
        rewrite Heq_vset; auto. 
    * split; auto. 
      intros; apply H. 
      sets_unfold. 
      rewrite Heq_vset; auto. 
  - destruct H as [[? _]|[]]; [left|right]. 
    * split; [|destruct z2; simpl; auto]. 
      destruct H as [p [[Hvalid Hmin] Hpeq]]. 
      exists p; split; auto. 
      split. 
      + sets_unfold. 
        rewrite Heq_vset; auto. 
      + intros q Hq. 
        apply Hmin. 
        sets_unfold. 
        rewrite <- Heq_vset; auto. 
    * split; auto. 
      intros; apply H. 
      sets_unfold. 
      rewrite <- Heq_vset; auto. 
Qed. 

Theorem min_value_weight_epath_unique: 
  forall u v z1 z2,
    min_value_weight_epath g u v z1 ->
    min_value_weight_epath g u v z2 ->
    z1 = z2.
Proof.
  intros. 
  destruct H as [[]|[]]; 
  destruct H0 as [[]|[]]; subst.
  - eapply min_unique; eauto; apply Z_op_le_TotalOrder.
  - destruct z1; auto. 
    destruct H as [p [[Hvalid _] Heq]]. 
    pose proof H0 p Hvalid. 
    rewrite Heq in H; simpl in H; contradiction.
  - destruct z2; auto. 
    destruct H0 as [p [[Hvalid _] Heq]]. 
    pose proof H p Hvalid. 
    rewrite Heq in H0; simpl in H0; contradiction.
  - auto.
Qed.

Lemma min_value_weight_epath_in_vset_subset:
  forall u v S1 S2 z1 z2, 
    min_value_weight_epath_in_vset g u v S1 z1 ->
    S1 ⊆ S2 ->
    min_value_weight_epath_in_vset g u v S2 z2 ->
    Z_op_le z2 z1.
Proof.
  intros. 
  destruct H as [[? _]|[]]; 
  destruct H1 as [[? _]|[]]; subst.
  - destruct H as [p [[Hpvalid Hpmin] Hpeq]]. 
    destruct H1 as [q [[Hqvalid Hqmin] Hqeq]]. 
    eapply is_epath_through_vset_subset in Hpvalid; eauto.  
    pose proof Hqmin p Hpvalid. 
    rewrite <- Hpeq, <- Hqeq; auto. 
  - destruct H as [p [[Hpvalid Hpmin] Hpeq]]. 
    eapply is_epath_through_vset_subset in Hpvalid; eauto. 
    pose proof H1 p Hpvalid. 
    rewrite Hpeq in H; auto. 
  - destruct z2; simpl; auto. 
  - simpl; auto. 
Qed. 

Lemma min_value_weight_epath_in_vset_universe:
  forall u v S z1 z2, 
    min_value_weight_epath g u v z1 ->
    min_value_weight_epath_in_vset g u v S z2 ->
    Z_op_le z1 z2.
Proof.
  intros.
  destruct H as [[? _]|[]]; 
  destruct H0 as [[? _]|[]]; subst.
  - destruct H as [p [[Hpvalid Hpmin] Hpeq]]. 
    destruct H0 as [q [[Hqvalid Hqmin] Hqeq]]. 
    destruct Hqvalid as [? _]. 
    pose proof Hpmin q H. 
    rewrite <- Hpeq, <- Hqeq; auto. 
  - destruct z1; simpl; auto. 
  - destruct H0 as [p [[Hpvalid Hpmin] Hpeq]]. 
    destruct Hpvalid as [? _]. 
    pose proof H p H0. 
    rewrite Hpeq in H1; auto. 
  - simpl; auto. 
Qed. 

Theorem min_value_weight_epath_in_vset_determin: 
  forall u v S1 S2 z1 z2,
    min_value_weight_epath g u v z1 ->
    min_value_weight_epath_in_vset g u v S1 z1 ->
    S1 ⊆ S2 ->
    min_value_weight_epath_in_vset g u v S2 z2 ->
    z1 = z2.
Proof.
  intros.
  pose proof min_value_weight_epath_in_vset_subset _ _ _ _ _ _ H0 H1 H2 as Hge.
  pose proof min_value_weight_epath_in_vset_universe _ _ _ _ _ H H2 as Hle.
  destruct z1; destruct z2; simpl in *; try f_equal; try lia; auto.
Qed.

End EPATH.