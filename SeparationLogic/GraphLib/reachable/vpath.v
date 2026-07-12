Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Positional.
From GraphLib Require Import graph_basic reachable_basic path.
From ListLib Require Import Base.Inductive General.NoDup.

Import SetsNotation.

Local Open Scope sets.

Section VPATH.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

(* 基于原始Type Class destruct1n的导出定义valid_vpath在list V上的归纳法 *)

(* vpath: 存在一个P，使得P的vertexList等于它 *)
Definition valid_vpath: 
  G -> V -> list V -> V -> Prop := 
  fun g u p v => exists P: P, 
    path_valid g P /\ 
    vertex_in_path P = p /\ 
    head P = u /\ 
    tail P = v.

(* 不存在空list V的vpath *)
Lemma valid_vpath_not_nil:
  forall g u p v,
  valid_vpath g u p v ->
  p <> nil.
Proof.
  intros.
  destruct H as [Pp [Hp [Hv [Hh Ht]]]].
  destruct p. 
  - apply Some_injection in Hh.
    erewrite head_valid in Hh; eauto.
    rewrite Hv in Hh; inversion Hh.
  - symmetry.
    apply nil_cons.
Qed.

(* empty_path能构造出平凡的vpath *)
Lemma valid_vpath_empty: forall g v,
    valid_vpath g v (v :: nil) v.
Proof.
  intros. 
  assert (Hvalid: path_valid g (empty_path v)) by (apply empty_path_valid).
  exists (empty_path v). 
  split; [|split; [|split]]; auto.
  - apply empty_path_vertex.
  - apply Some_inversion. 
    erewrite head_valid; eauto. 
    rewrite empty_path_vertex. 
    reflexivity.
  - apply Some_inversion. 
    erewrite tail_valid; eauto. 
    rewrite empty_path_vertex. 
    reflexivity.
Qed.

(* singleton的vpath对应首尾相等的empty_path *)
Lemma valid_vpath_empty_inv:
  forall g u x v,
  valid_vpath g u (x :: nil) v ->
  u = x /\ v = x.
Proof.
  intros.
  destruct H as [Pp [Hp [Hv [Hh Ht]]]].
  apply Some_injection in Hh, Ht.
  erewrite head_valid in Hh; eauto.
  erewrite tail_valid in Ht; eauto.
  rewrite Hv in Hh, Ht. inversion Hh; inversion Ht.
  subst; auto.
Qed.

(* single_path能构造出单步的vpath *)
Lemma single_vpath_valid: forall g u v,
  step g u v ->
  valid_vpath g u (u :: v :: nil) v.
Proof.
  intros. 
  destruct H as [e Hstep]. 
  assert (Hvalid: path_valid g (single_path u v e)) by (apply single_path_valid; auto).
  exists (single_path u v e). 
  split; [|split; [|split]]; auto.
  - rewrite single_path_vertex. 
    reflexivity.
  - apply Some_inversion. 
    erewrite head_valid; eauto. 
    rewrite single_path_vertex. 
    reflexivity. 
  - apply Some_inversion. 
    erewrite tail_valid; eauto. 
    rewrite single_path_vertex. 
    reflexivity.
Qed.

(* 两个元素的vpath对应single_path *)
Lemma valid_vpath_single_inv:
  forall g u x y v,
  valid_vpath g u (x :: y :: nil) v ->
  u = x /\ v = y /\ step g x y.
Proof.
  intros.
  destruct H as [Pp [Hp [Hv [Hh Ht]]]].
  apply Some_injection in Hh, Ht.
  erewrite head_valid in Hh; eauto.
  erewrite tail_valid in Ht; eauto.
  rewrite Hv in Hh, Ht. inversion Hh; inversion Ht.
  subst; split; [|split]; auto. 
  destruct (edge_in_path Pp) eqn: Hle. 
  - exfalso. 
    pose proof vpath_iff_epath g Pp Hp as [? _]. 
    rewrite Hv, Hle in *. 
    simpl in *. lia.
  - pose proof vpath_iff_epath g Pp Hp as [_ Hpstep]. 
    specialize (Hpstep 0 u v e ltac:(rewrite Hle; simpl; lia) ltac:(rewrite Hle; simpl; auto)
    ltac:(rewrite Hv; simpl; auto) ltac:(rewrite Hv; simpl; auto)). 
    eapply step_trivial; eauto.
Qed.

(* vpath的++也是vpath *)
Lemma valid_vpath_app:
  forall g u p1 v p2 w,
  valid_vpath g u p1 v ->
  valid_vpath g v p2 w ->
  valid_vpath g u (p1 ++ tl p2) w.
Proof.
  intros.
  destruct H as [P1 [Hp1 [Hv1 [Hh1 Ht1]]]].
  destruct H0 as [P2 [Hp2 [Hv2 [Hh2 Ht2]]]].
  subst.
  exists (concat_path P1 P2).
  assert (Hvalid: path_valid g (concat_path P1 P2)) by (apply concat_path_valid; auto). 
  split; [|split; [|split]]; auto.
  - apply concat_path_vertex.
  - apply Some_inversion.
    repeat erewrite head_valid; eauto. 
    rewrite concat_path_vertex. 
    apply Some_injection in Hh2. 
    erewrite head_valid in Hh2; eauto. 
    erewrite tail_valid in Hh2; eauto.
    unfold tl_error in Hh2. 
    destruct (vertex_in_path P1); simpl in *; auto. 
    destruct (vertex_in_path P2); simpl in *; auto. 
    congruence. 
  - apply Some_inversion.
    repeat erewrite tail_valid; eauto.
    rewrite concat_path_vertex. 
    unfold tl_error. 
    apply Some_injection in Hh2. 
    erewrite head_valid in Hh2; eauto. 
    erewrite tail_valid in Hh2; eauto. 
    unfold tl_error in Hh2. 
    destruct (vertex_in_path P2); simpl in *; auto. 
    * destruct (vertex_in_path P1); simpl in *; auto. 
      rewrite app_nil_r; auto. 
    * destruct l.
      + rewrite app_nil_r; auto. 
      + rewrite length_app. 
        rewrite nth_error_app2. 
        2: simpl; lia. 
        simpl. 
        replace ((length (vertex_in_path P1) + S (length l) - 1 - length (vertex_in_path P1))) with (length l) by lia. auto. 
Qed.


(* vpath能够被1n分解，即平凡的单步或单步++vpath *)
Lemma valid_vpath_inv_1n:
  forall g u p v,
  valid_vpath g u p v ->
  (u = v /\ p = u :: nil) \/
  (exists w p', p = u :: p' /\ step g u w /\ valid_vpath g w p' v).
Proof.
  intros g u p v [Pp [Hvalid [Hvert [Hhd Htl]]]].
  pose proof (destruct_1n_spec g Pp Hvalid) as Hspec.
  destruct (destruct_1n_path g Pp Hvalid) eqn: ?; 
  unfold path_cons_spec in *.
  - (* Case: Base Path *)
    subst Pp.
    rewrite empty_path_vertex in *.
    apply Some_injection in Hhd; erewrite head_valid in Hhd by eauto.
    apply Some_injection in Htl; erewrite tail_valid in Htl by eauto.
    rewrite empty_path_vertex in *; inversion Hhd; inversion Htl.
    left; subst; auto.
  - (* Case: Step Path *)
    destruct Hspec as [Hp' [Hhd' [Hstep Heq]]]; subst Pp.
    assert (Hnn: vertex_in_path p0 <> nil).
    { intro Hn. apply head_valid in Hp'. rewrite Hn in Hp'. inversion Hp'. }
    destruct (vertex_in_path p0) as [|w vs] eqn:Hv0; [congruence|].
    
    apply Some_injection in Hhd'. 
    erewrite head_valid in Hhd' by eauto.
    rewrite Hv0 in Hhd'. inversion Hhd'.
    
    rewrite concat_path_vertex, single_path_vertex in Hvert.
    rewrite Hv0 in Hvert. simpl in Hvert.
    
    apply Some_injection in Hhd. 
    erewrite head_valid in Hhd; eauto. 
    rewrite concat_path_vertex in Hhd.
    rewrite single_path_vertex in Hhd.
    rewrite Hv0 in Hhd. inversion Hhd.
    subst.
    
    right.
    (* 构造右侧分支的 witness *)
    exists v0, (v0 :: vs).
    split; [auto | split; [exists e; auto|]].
    exists p0. repeat split; auto.
    * apply Some_inversion. 
      erewrite head_valid; eauto. 
      rewrite Hv0. 
      reflexivity. 
    * apply Some_inversion.
      erewrite !tail_valid; eauto. 
      rewrite concat_path_vertex.
      rewrite single_path_vertex.
      rewrite Hv0. 
      destruct (list_snoc_destruct vs); 
      [subst; simpl in *; reflexivity|simpl].
      destruct H as [? []]; subst.
      rewrite !app_comm_cons.
      rewrite !tl_error_last; reflexivity.
Qed.

(* cons构成的vpath能够分解出一个单步 *)
Lemma valid_vpath_cons_inv:
  forall g u p v,
  valid_vpath g u (u :: p) v ->
  (p = nil /\ u = v) \/ exists w, step g u w /\ valid_vpath g w p v.
Proof.
  intros. 
  apply valid_vpath_inv_1n in H as [(-> & ?) | (w & p' & ? & ? & ?)]. 
  - left; inversion H; tauto.
  - right; exists w. 
    inversion H; subst. 
    split; auto.
Qed.

(* 额外性质：vpath的head必须与起始节点相同 *)
Lemma valid_vpath_start:
  forall g u p v,
  valid_vpath g u p v ->
  exists p', p = u :: p'.
Proof.
  intros.
  pose proof (valid_vpath_inv_1n _ _ _ _ H) as [(-> & ->) | (w & p' & -> & ? & ?)].
  eauto. eauto.
Qed.

(* vpath的单步cons也是vpath *)
Lemma valid_vpath_cons:
  forall g u v p w,
  step g u v ->
  valid_vpath g v p w ->
  valid_vpath g u (u :: p) w.
Proof.
  intros.
  pose proof (valid_vpath_start _ _ _ _ H0) as (p' & ->).
  eapply (valid_vpath_app g u (u :: v :: nil) v (v :: p') w).
  apply single_vpath_valid. auto. auto.
Qed.

(* ++构成的vpath能够被拆散 *)
Lemma valid_vpath_app_inv:
  forall g u p1 v p2 w,
  valid_vpath g u (p1 ++ v :: p2) w ->
  valid_vpath g u (p1 ++ v :: nil) v /\ valid_vpath g v (v :: p2) w.
Proof.
  intros g u p1 v p2 w.
  generalize dependent u.
  induction p1 as [|x xs IH]; simpl; intros.
  - (* Base Case: p1 = [] *)
    destruct H as [Pp [Hp [Hvert [Hhd Htl]]]].
    assert (u = v). {
      apply Some_injection in Hhd. 
      erewrite head_valid in Hhd; eauto.
      rewrite Hvert in Hhd. 
      injection Hhd; auto.
    }
    subst; split.
    + apply valid_vpath_empty.
    + exists Pp; auto.
  - apply valid_vpath_inv_1n in H.
    destruct H as [[? Heq] | [y [p' [Heq [Hstep Hsub]]]]].
    + (* Case: p 是单点，不可能包含 v :: p2 *)
      subst. destruct xs; inversion Heq.
    + (* Case: p = u -> y -> ... *)
      inversion Heq; subst.
      apply IH in Hsub. 
      destruct Hsub as [Hleft Hright].
      split; auto.
      pose proof valid_vpath_cons g u y 
      (xs ++ v :: nil) v Hstep Hleft.
      pose proof valid_vpath_app g u (u :: nil) u (u :: xs ++ v :: nil) v
      ltac:(eapply valid_vpath_empty; auto) H. 
      simpl in H0. 
      auto.
Qed.

(* vpath上对list V的1n归纳法则 *)
Theorem valid_vpath_ind_1n:
  forall g (P : V -> list V -> V -> Prop),
  (forall v, P v (v :: nil) v) ->
  (forall u v p w,
   step g u v -> valid_vpath g v p w -> P v p w ->
   P u (u :: p) w) ->
  forall u p v, valid_vpath g u p v -> P u p v.
Proof.
  intros g Pp IH1 IH2 u p' v H.
  pose proof (valid_vpath_start _ _ _ _ H) as (p & ->).
  revert u v H. induction p; intros.
  - pose proof (valid_vpath_inv_1n _ _ _ _ H) as [(-> & ?) | (w & p' & ? & ? & ?)].
    apply IH1.
    inversion H0. subst.
    pose proof (valid_vpath_inv_1n _ _ _ _ H2) as [(? & ?) | (? & ? & ? & ? & ?)].
    congruence. congruence.
  - pose proof (valid_vpath_inv_1n _ _ _ _ H) as [(-> & ?) | (w & p' & ? & ? & ?)].
    congruence.
    inversion H0. subst. 
    pose proof (valid_vpath_start _ _ _ _ H2) as (p' & ?). inversion H3. subst.
    eapply IH2; eauto.
Qed.

(* vpath上对list V的n1归纳法则 *)
Theorem valid_vpath_ind_n1:
  forall g (P : V -> list V -> V -> Prop),
  (forall v, P v (v :: nil) v) ->
  (forall u p v w,
   valid_vpath g u p v -> P u p v -> step g v w ->
   P u (p ++ w :: nil) w) ->
  forall u p v, valid_vpath g u p v -> P u p v.
Proof.
  intros g Pp IH1 IH2.
  enough (forall u p1 v p2 w,
          valid_vpath g u p1 v ->
          Pp u p1 v ->
          valid_vpath g v p2 w ->
          Pp u (p1 ++ tl p2) w).
  { intros. specialize (H u (u :: nil) u p v).
    pose proof (valid_vpath_start _ _ _ _ H0) as (p' & ->).
    apply H; auto. apply valid_vpath_empty.  }
  intros * Hp1 Hp1' Hp2.
  revert u p1 Hp1 Hp1'.
  pattern v, p2, w. revert v p2 w Hp2.
  eapply valid_vpath_ind_1n; eauto.
  - simpl. intros. rewrite app_nil_r. auto.
  - simpl. intros.
    pose proof (valid_vpath_start _ _ _ _ H0) as (p2 & ->).
    replace (p1 ++ v :: p2) with ((p1 ++ v :: nil) ++ p2).
    2:{ rewrite <- app_assoc. auto. }
    apply H1.
    eapply valid_vpath_app with (p2 := u :: v :: nil); eauto.
    apply single_vpath_valid; auto.
    eapply IH2; eauto.
Qed.

(* vpath能够被n1分解，即平凡的单步或vpath++单步 *)
Lemma valid_vpath_inv_n1:
  forall g u p v,
  valid_vpath g u p v ->
  (u = v /\ p = u :: nil) \/
  (exists p' w, p = p' ++ v :: nil /\ valid_vpath g u p' w /\ step g w v).
Proof.
  intros.
  revert u p v H. eapply valid_vpath_ind_n1; eauto.
  intros. right. eauto.
Qed.

(* 额外性质：vpath的tail必须为终止节点 *)
Lemma valid_vpath_end:
  forall g u p v,
  valid_vpath g u p v ->
  exists p', p = p' ++ v :: nil.
Proof.
  intros.
  pose proof (valid_vpath_inv_n1 _ _ _ _ H) as [(-> & ->) | (w & p' & -> & ? & ?)].
  exists nil. easy. eauto.
Qed.

(* vpath的尾部接上单步也是vpath *)
Lemma valid_vpath_snoc:
  forall g u p v w,
  valid_vpath g u p v ->
  step g v w ->
  valid_vpath g u (p ++ w :: nil) w.
Proof.
  intros.
  pose proof (valid_vpath_end _ _ _ _ H) as (p' & ->).
  eapply (valid_vpath_app g u (p' ++ v :: nil) v (v :: w :: nil) w).
  auto. apply single_vpath_valid. auto.
Qed.

(* vpath能够从尾部拆分 *)
Lemma valid_vpath_snoc_inv:
  forall g u p z v,
  valid_vpath g u (p ++ z :: v :: nil) v ->
  valid_vpath g u (p ++ z :: nil) z /\ step g z v.
Proof.
  intros g u p z v H.
  apply valid_vpath_app_inv in H.
  destruct H as [Hpath_uz Hstep_zv].
  split.
  - exact Hpath_uz.
  - apply valid_vpath_single_inv in Hstep_zv.
    destruct Hstep_zv as (? & ? & Hstep).
    exact Hstep.
Qed.

(* vpath能够被转换为reachable *)
Lemma valid_vpath_reachable:
  forall g u p v,
  valid_vpath g u p v ->
  reachable g u v.
Proof.
  intros g. eapply valid_vpath_ind_1n; intros.
  - reflexivity.
  - unfold reachable.
    pose proof (rt_trans_1n (step g)). sets_unfold in H2.
    apply H2. eauto.
Qed.

(* reachable能够被转换为vpath *)
Lemma reachable_valid_vpath:
  forall g u v,
  reachable g u v ->
  exists p, valid_vpath g u p v.
Proof.
  intros. unfold reachable in H.
  induction_1n H.
  - exists (v :: nil). apply valid_vpath_empty.
  - destruct IHrt as (p & ?).
    exists (u :: p). eapply valid_vpath_cons; eauto.
Qed.

(* vpath上的简单路径：不经过重复顶点 *)
Definition is_simple_vpath (g: G) (u: V) (p: list V) (v: V): Prop :=
  valid_vpath g u p v /\ NoDup p.

(* 移除vpath中的环 *)
Lemma valid_vpath_remove_cycle: 
  forall g u v l1 x l2 l3,
  valid_vpath g u (l1 ++ x :: l2 ++ x :: l3) v ->
  valid_vpath g u (l1 ++ x :: l3) v.
Proof.
  intros.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H. 
  apply valid_vpath_app_inv in H as [H_first_part H_tail].
  rewrite <- !app_assoc in H_first_part. 
  rewrite <- app_comm_cons in H_first_part.
  apply valid_vpath_app_inv in H_first_part.
  destruct H_first_part as [H_head _]. 
  pose proof (valid_vpath_app g u (l1 ++ x :: nil) x (x :: l3) v H_head H_tail).
  simpl in H. 
  rewrite <- app_assoc in H. 
  exact H.
Qed.

(* 任意两点之间的vpath能够被转换为简单的vpath *)
Theorem valid_vpath_simple:
  forall g u p v,
  valid_vpath g u p v ->
  exists q, is_simple_vpath g u q v.
Proof.
  intros g u p v H_valid.
  remember (length p) as n.
  revert u p v H_valid Heqn.
  induction n using lt_wf_ind; intros u p v H_valid Heqn.
  destruct (classic (NoDup p)).
  - exists p. split; auto.
  - apply Nodup_exists_repetition in H0.
    destruct H0 as [x [l1 [l2 [l3 H_eq]]]].
    subst p.
    set (p' := l1 ++ x :: l3).
    assert (H_valid_p': valid_vpath g u p' v).
    { unfold p'. eapply valid_vpath_remove_cycle. eassumption. }
    assert (H_len: length p' < length (l1 ++ x :: l2 ++ x :: l3)). {
      unfold p'.
      rewrite !length_app; simpl.
      rewrite !length_app; simpl.
      lia. }
    apply (H (length p')) in H_valid_p'; auto; lia.
Qed.

(* 这里先尝试一下两种through vset的定义是否等价，然后再测试一下是否好用。 *)
(* vset就等于path去掉首尾后的所有点的集合 *)
Definition is_vpath_through_exactly_vset 
  (g: G) (u: V) (p: list V) (v: V) (vset: V -> Prop): Prop :=
  valid_vpath g u p v /\ 
  forall x, x ∈ vset <-> 
  exists p1 p2, 
    valid_vpath g u (u :: p1 ++ x :: nil) x /\ 
    valid_vpath g x (x :: p2 ++ v :: nil) v /\ 
    (u :: p1) ++ x :: (p2 ++ v :: nil) = p . 

Theorem is_vpath_through_exactly_vset_correct: 
  forall g u p v, 
  valid_vpath g u p v ->
  is_vpath_through_exactly_vset g u p v (fun x => In x (removelast (tl p))).
Proof.
  intros; split; [auto|split; intros]. 
  - destruct p. 
    1:{ exfalso. exact H0. } 
    simpl in H0.
    destruct (list_snoc_destruct p) as [|[? []]]; subst. 
    1:{ exfalso. exact H0. } 
    rewrite removelast_last in H0.  
    apply in_split in H0 as [l1 [l2 H0]]; subst. 
    assert (u = v0) by 
    (apply valid_vpath_start in H as [? Heq]; inversion Heq; reflexivity); subst v0.  
    assert (v = x0) by  
    (apply valid_vpath_end in H as [? Heq]; 
    rewrite app_comm_cons in Heq;
    apply app_inj_tail_iff in Heq as []; auto); subst x0. 

    rewrite <- app_assoc in H.
    rewrite app_comm_cons in H. 
     
    exists l1, l2; repeat split.

    * apply valid_vpath_app_inv in H as [? _]; auto. 
    * apply valid_vpath_app_inv in H as [_ ?]; auto. 
    * simpl; rewrite <- !app_assoc. 
      rewrite <- !app_comm_cons.  
      reflexivity. 
  - destruct H0 as [p1 [p2 [Hp1 [Hp2 Heq]]]]; subst. 
    simpl; rewrite app_comm_cons. 
    rewrite app_assoc. 
    rewrite removelast_last. 
    apply in_or_app; right. 
    apply in_eq.
Qed.
    

End VPATH.

