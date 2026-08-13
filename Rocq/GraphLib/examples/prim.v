Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Export Coq.Classes.EquivDec.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.path_basic.
Require Import GraphLib.reachable.vpath.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.undirected.tree.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import General.NoDup General.Forall.

Import ListNotations.

Local Open Scope sets.
Local Open Scope Z.

Section prim.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {elistbijective: EListBijective G V E}
        {simplegraph: SimpleGraph G V E}
        {addLeafExist: addLeafExist G V E}
        {addEdgeExist: addEdgeExist G V E}. (*要求原图的加边存在性*)
Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.
Context (g: G)
        {g_valid: gvalid g}
        {g_tree: tree g}.

Context (r: G)
        {r_valid: gvalid r}
        {ew: EdgeWeight G E}.

Lemma tree_addEdge_have_circuit: 
  forall i h u v e, 
    gvalid i ->
    tree i -> 
    vvalid i u -> vvalid i v -> ~ evalid i e ->
    addEdge i h u v e -> 
    exists p, is_simple_epath h u p u /\ In e p /\ p <> nil.
Proof. 
  intros i h u v e Hvalid Htree Hu Hv He Hadd. 
  pose proof Hadd as [Hvvalid Hevalid Hstep_aux]. 
  pose proof tree_connected i Htree u v Hu Hv.
  apply reachable_valid_epath in H as [p Hpath]. 
  eapply valid_epath_simple in Hpath.
  2:{ intros; eapply step_aux_unique_undirected; try apply Hvalid; eauto. }
  destruct Hpath as [q [Hqsimple Hqnodup]]. 
  exists (q ++ [e]); split; [|split];
  [split | apply in_app_iff; right; simpl; auto | symmetry; apply app_cons_not_nil].
  * eapply valid_epath_snoc with (v:=v); eauto.
    + eapply addEdge2_valid_epath; eauto.
    + apply Hstep_aux; right; split; auto. 
  * apply Nodup_app_comm. 
    simpl; constructor; auto. 
    assert (forall a, In a q -> evalid i a). {
      intros a Hin. 
      apply in_split in Hin as [l1 [l2 Hp]]; subst. 
      apply valid_epath_app_inv in Hqsimple as [b [Hl1 Hrest]].
      apply valid_epath_cons_inv in Hrest as [c [Hstep Hl2]].
      eapply step_evalid; eauto.
    }
    unfold not; intros; apply He; auto. 
Qed.


Lemma addEdge2_replace_edge_connected:
  forall y1 h i u v e x y a p,
    gvalid y1 ->
    gvalid h ->
    tree y1 -> 
    vvalid y1 u ->  
    vvalid y1 v ->
    addEdge y1 h u v e ->
    ~ evalid i a -> 
    addEdge i h x y a ->
    is_simple_epath h u p u ->
    In a p ->
    connected i.
Proof.
  intros y1 h i u v e x y a p Hvalid_y1 Hvalid_h Htree_y1 Hu Hv Hadd2 Hanoitini Hi Hp Hina s t Hs Ht.
  assert (Hs_y1 : vvalid y1 s) by (erewrite <- (addEdge2_vvalid_iff y1 h u v e); eauto; apply Hi; eauto).
  assert (Ht_y1 : vvalid y1 t) by (erewrite <- (addEdge2_vvalid_iff y1 h u v e); eauto; apply Hi; eauto).

  destruct (reachable_valid_epath _ _ _ (tree_connected _ Htree_y1 _ _ Hs_y1 Ht_y1)) as [q Hqpath].
  eapply valid_epath_simple in Hqpath as [q' [Hq'path Hq'nodup]].
  2:{ intros; eapply step_aux_unique_undirected; try apply Hvalid_y1; eauto. }

  destruct (classic (In a q')) as [Hinaq | Hnotinaq].
  - apply in_split in Hinaq as [q1 [q2]]; subst.
    apply valid_epath_app_inv in Hq'path as [z [Hpre Hrest]].
    apply valid_epath_cons_inv in Hrest as [w [Hstep_a Hpost]]. 
    eapply addEdge2_old_step in Hstep_a as Hstep_a_h; eauto. 
    eapply addEdge2_new_step_uv in Hi as Hstep_a_new; eauto. 
    eapply step_aux_unique_undirected in Hstep_a_h as [[]|[]]; eauto; subst z w.
    + eapply addEdge2_cycle_without_new_edge_simple in Hina as [alt [[Halt_path _] _]]; eauto.
      eapply valid_epath_reachable.
      eapply valid_epath_app; [|eapply valid_epath_app].
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (g1:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [Hnotin1 _]; contradiction.
      * exact Halt_path.
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (g1:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [_ Hnotin2]; contradiction.
    + eapply addEdge2_cycle_without_new_edge_simple in Hina as [alt [[Halt_path _] _]]; eauto.
      eapply valid_epath_reachable.
      eapply valid_epath_app; [|eapply valid_epath_app].
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (g1:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [Hnotin1 _]; contradiction.
      * apply valid_epath_rev. exact Halt_path.
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (g1:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [_ Hnotin2]; contradiction.
  - eapply valid_epath_reachable.
    eapply addEdge2_valid_epath_new_to_old; [exact Hi| |exact Hnotinaq].
    eapply addEdge2_valid_epath with (g1:=y1); eauto. 
  Unshelve. all: auto.
Qed.

Lemma addEdge2_delete_circuit_no_circuit:
  forall y1 h i u v e x y a p,
    gvalid y1 ->
    gvalid h ->
    tree y1 -> 
    ~ evalid y1 e ->
    addEdge y1 h u v e ->
    ~ evalid i a ->
    addEdge i h x y a ->
    is_simple_epath h u p u ->
    In e p ->
    In a p ->
    a <> e ->
    ~ exists z q, q <> nil /\ is_simple_epath i z q z.
Proof.
  intros y1 h i u v e x y a p Hvalid_y1 Hvalid_h Htree_y1 He Hadd2 Ha Hi Hp Hein Hina Hane [z [q [Hqne Hq]]].
  assert (Hq_h : is_simple_epath h z q z) by (destruct Hq as [Hqpath Hqnodup]; split; auto; eapply addEdge2_valid_epath; eauto).
  destruct (classic (In e q)) as [Heinq | Hnotinq].
  - eapply addEdge2_cycle_without_new_edge_simple in Hein as [p_old [Hp_old Hp_mem]]; eauto.
    eapply addEdge2_cycle_without_new_edge_simple in Heinq as [q_old [Hq_old Hq_mem]]; eauto.
    assert (Hpq : p_old = q_old) by (eapply tree_one_simple_epath with (g:= y1); eauto).
    assert (Hain_pold : In a p_old) by (apply Hp_mem; split; auto).
    assert (Hnotin_q : ~ In a q) by (eapply addEdge2_edge_not_in_old_path; eauto; apply Hq).
    assert (Hnotin_qold : ~ In a q_old) by (intro Hain; apply Hq_mem in Hain as [Hainq _]; contradiction).
    subst q_old. contradiction.
  - eapply tree_no_curcuit; eauto.
    exists z, q; split; auto.
    destruct Hq as [Hqpath Hqnodup].
    split; auto.
    eapply addEdge2_valid_epath_new_to_old ; eauto. 
    apply Hq_h.
Qed.

Lemma addEdge2_delete_circuit_tree:
  forall y1 h i u v e x y a p,
    gvalid y1 ->
    gvalid h ->
    tree y1 -> 
    (vvalid y1 u /\ vvalid y1 v /\ ~ evalid y1 e) ->
    addEdge y1 h u v e -> 
    ~ evalid i a ->
    addEdge i h x y a ->
    is_simple_epath h u p u ->
    In e p ->
    In a p ->
    a <> e ->
    tree i.
Proof.
  intros.
  apply tree_decide.
  - eapply addEdge2_replace_edge_connected with (y1:=y1); eauto; tauto.
  - eapply addEdge2_delete_circuit_no_circuit with (y1:=y1); eauto; tauto.
Qed.

Lemma circuit_have_pair_cross_edge: 
  forall i h u v e p, 
    gvalid h ->
    vvalid i u -> ~ vvalid i v -> step_aux h e u v -> 
    In e p -> 
    is_simple_epath h u p u ->
    exists x y a, vvalid i x /\ ~ vvalid i y /\ step_aux h a x y /\ In a p /\ a <> e.
Proof.
  intros i h u v e p Hvalid_h Hu Hv Hstep_e Hin [Hpath Hnodup].
  apply in_split in Hin as [p1 [p2 Hp]].
  subst p.
  apply valid_epath_app_inv in Hpath as [z [Hpre Hrest]].
  apply valid_epath_cons_inv in Hrest as [w [Hstep_in Hpost]]. 
  eapply step_aux_unique_undirected in Hstep_e as [[Hzu Hwv] | [Hwu Hzv]]; eauto; subst.
  - pose proof (valid_epath_rev h v p2 u Hpost) as Hrev. 
    eapply valid_epath_cross with (P := vvalid i) in Hrev
    as [x [y [a [Hx [Hy [Hstep Hina]]]]]]; eauto.
    exists x, y, a; repeat split; auto.
    + rewrite in_app_iff; right; simpl; right; apply in_rev; auto. 
    + destruct (Nodup_split_constructors p1 p2 e Hnodup) as [_ Hnotin].
      intro Heq; subst; apply Hnotin; apply in_rev; auto. 
  - eapply valid_epath_cross with (P := vvalid i) in Hpre
    as [x [y [a [Hx [Hy [Hstep Hina]]]]]]; eauto.
    exists x, y, a; repeat split; auto.
    + rewrite in_app_iff; left; auto.
    + destruct (Nodup_split_constructors p1 p2 e Hnodup) as [Hnotin _].
      intro Heq; subst; contradiction.
Qed.


Theorem prim_step: 
  forall g1 g2 u v e, 
    gvalid g1 /\ tree g1 /\ (exists y1, is_mst r y1 /\ subgraph2 g1 y1) -> 
    step_aux r e u v -> 
    vvalid g1 u -> ~ vvalid g1 v ->
    addEdge g1 g2 u v e -> 
    min_object_of_subset Z_op_le (fun e => exists u v, vvalid g1 u /\ ~ vvalid g1 v /\ step_aux r e u v) (weight r) e ->
    (exists y2, is_mst r y2 /\ subgraph2 g2 y2). 
Proof. 
  intros g1 g2 u v e [Hgvalid1 [Htree [y1 [Hmst Hsubgraph]]]] Hrstep Hu Hv Hadd Hmin. 
  destruct (classic (evalid y1 e)).
  - exists y1; split; auto. 
    split. 
    { 
      intros x Hx. 
      apply Hadd in Hx as [|[|]]; subst. 
      + apply Hsubgraph; auto. 
      + apply Hmst. 
        eapply step_vvalid1; eauto. 
      + apply Hmst. 
        eapply step_vvalid2; eauto.  
    } 
    {
      intros x y a Hstep.
      destruct Hadd as [Hvvalid Hevalid Hstep_aux].
      apply Hstep_aux in Hstep as [Hold | [Heq [[Hx Hy] | [Hx Hy]]]]; subst.
      + apply Hsubgraph; auto.
      + eapply mst_edge_step with (r:=r); eauto.
      + apply step_sym. eapply mst_edge_step with (r:=r); eauto.
    }
  - (* 当新增加的边e不在原来的被包含在的最小生成树中时 *)
    (* 将这条边e增加到最小生成树y1中去，y1 + e = h *) 
    assert (Huy1: vvalid y1 u) by (apply Hsubgraph; auto).
    assert (Hvy1: vvalid y1 v) by (apply Hmst; eapply step_vvalid2; eauto). 
    assert (exists h, gvalid h /\ addEdge y1 h u v e) as [h [Hvalid Hadd2]].
    {
      apply addEdge_valid; auto. 
      apply Hmst.
    } 
    (* 则 h 中有一个简单回路 p ，包含跨边e *)
    assert (exists p, is_simple_epath h u p u /\ In e p /\ p <> nil) as [p [Hp [Heinp Hpne]]]. 
    {
      eapply tree_addEdge_have_circuit. 
      6: apply Hadd2. 
      all: try apply Hmst; try auto. 
      eapply step_vvalid1; eauto. 
      eapply step_vvalid2; eauto. 
    } 
    (* p 中包含另外一条跨边 a *)
    assert (exists x y a, vvalid g1 x /\ ~ vvalid g1 y /\ step_aux h a x y /\ In a p /\ a <> e) as [x [y [a [Hx [Hy [Hstep Hin]]]]]].
    {
      eapply circuit_have_pair_cross_edge with (v := v); eauto; 
      try (try destruct Hadd; tauto). 
      destruct Hadd2 as [_ _ Hstep_aux]. 
      apply Hstep_aux; right; auto.
    }
    (* 将 a 从 h 中删除，y1 + e - a = i *)
    assert (exists i, gvalid i /\ addEdge i h x y a /\ (vvalid i x /\ vvalid i y /\ ~ evalid i a)) as [i [Hvalidi [Hi [Hvx [Hvy Hnotina]]]]]. {
      apply addEdge_valid_inv; auto. 
      * eapply step_vvalid1; eauto.
      * eapply step_vvalid2; eauto.
      * eapply step_evalid; eauto.
    }
    
    
    (* i 是新的满足条件的最小生成树 *)
    exists i; split; [split; [split; [|split]|]|]. 

    (* i gvalid *)
    + apply Hvalidi. 


    (* i 是 树 *)
    + eapply (addEdge2_delete_circuit_tree y1 h i u v e x y a p). 
      all: try tauto.
      all: try apply Hmst. 


    (* i 是 原图的子图 *)
    + destruct Hmst as [Hy1_legal Hy1_min].
      destruct Hy1_legal as [_ [_ Hsubeq_y1]].
      destruct Hsubeq_y1 as [Hy1_vertex Hy1_step].
      split.
      * intros z.
        rewrite <- Hy1_vertex.
        erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
        apply addEdge2_vvalid_iff with (u := u) (v := v) (e := e); auto.  
      * intros z w b Hstep_i. 
        eapply addEdge2_old_step in Hstep_i as Hstep_h; try apply Hi; eauto.
        destruct Hadd2 as [_ _ Hstep_h_iff].
        apply Hstep_h_iff in Hstep_h as [Hstep_y1 | [Hb [[] | []]]]; subst; auto.
        apply step_sym; auto. 

    (* i 的权值小于等于 y1 的权值 *)
    + intros b Hb.
      eapply Z_op_le_trans with (y:= total_weight r y1); 
      [|apply Hmst; auto]. 
      pose proof Hadd2 as Hadd2'. 
      pose proof Hi as Hi'. 

      assert (Hadd2_perm: Permutation (bijective_listE h) (e :: bijective_listE y1)).
      {
        eapply addEdge_elist_permutation with
          (g1 := y1) (g2 := h) (u := u) (v := v) (e := e); eauto.
        - apply bijective_listE_NoDup. apply Hmst.
        - apply bijective_edges. apply Hmst.
        - apply bijective_listE_NoDup. exact Hvalid.
        - apply bijective_edges. exact Hvalid.
      }
      clear Hadd2; rename Hadd2_perm into Hadd2.

      assert (Hi_perm: Permutation (bijective_listE h) (a :: bijective_listE i)).
      {
        eapply addEdge_elist_permutation with
          (g1 := i) (g2 := h) (u := x) (v := y) (e := a); eauto.
        - apply bijective_listE_NoDup. exact Hvalidi.
        - apply bijective_edges. exact Hvalidi.
        - apply bijective_listE_NoDup. exact Hvalid.
        - apply bijective_edges. exact Hvalid.
      }
      clear Hi; rename Hi_perm into Hi.

      set (sumE := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight r) l)).
      assert (Hperm_sum : forall l1 l2, Permutation l1 l2 -> sumE l1 = sumE l2).
      {
        intros l1 l2 Hperm.
        induction Hperm; subst sumE; simpl; auto.
        - rewrite IHHperm; auto.
        - rewrite !Z_op_plus_assoc.
          rewrite (Z_op_plus_comm (weight r x0) (weight r y0)).
          reflexivity.
        - rewrite IHHperm1, IHHperm2; auto.
      }
      assert (Hh_y1 : total_weight r h = Z_op_plus (weight r e) (total_weight r y1)).
      {
        unfold total_weight. 
        pose proof (Hperm_sum _ _ Hadd2). 
        unfold sumE in H0. 
        (* rewrite H0. *)
        simpl in H0. 
        apply H0.
      }
      assert (Hh_i : total_weight r h = Z_op_plus (weight r a) (total_weight r i)).
      {
        unfold total_weight.
        pose proof (Hperm_sum _ _ Hi). 
        unfold sumE in H0. 
        rewrite H0.
        simpl; reflexivity.
      }
      destruct Hmst as [[Hy1_valid [_ Hsubeq_y1]] _].
      destruct Hsubeq_y1 as [_ Hy1_step].
      assert (Hstep_y1 : step_aux y1 a x y) by (eapply addEdge2_keep_step; eauto; tauto).
      assert (Hin_a_y1 : In a (bijective_listE y1)).
      { apply bijective_edges; auto. eapply step_evalid; eauto. }
      assert (Hwea : Z_op_le (weight r e) (weight r a)).
      {
        destruct Hmin as [_ Hmin_sound].
        apply Hmin_sound.
        exists x, y.
        repeat split; auto.
      }
      assert (Hnone_in_sum :
        forall l, In a l -> weight r a = None -> sumE l = None).
      {
        intros l.
        induction l as [|c l IH]; intros Hinc Hwa; simpl in *; [contradiction|].
        destruct Hinc as [Hc | Hinc].
        - subst. unfold sumE; simpl. rewrite Hwa. reflexivity.
        - apply IH in Hwa; auto. unfold sumE; simpl. 
          unfold sumE in Hwa; simpl in Hwa. 
          rewrite Hwa. apply Z_op_plus_none_r.
      }
      destruct (weight r a) as [wa|] eqn:Hwa.
      * destruct (weight r e) as [we|] eqn:Hwe; simpl in Hwea; [|contradiction].
        rewrite Hh_y1 in Hh_i.
        destruct (total_weight r i) as [wi|] eqn:Hwi;
        destruct (total_weight r y1) as [wy|] eqn:Hwy;
        simpl in *; try discriminate; auto.
        inversion Hh_i; subst; lia.
      * assert (Hy1_none : total_weight r y1 = None).
        {
          unfold total_weight.
          apply Hnone_in_sum; auto.
        }
        rewrite Hy1_none.
        apply Z_op_le_none_r.

    (* g2 是 i 的子图 *)
    + split.
      {
        intros z Hz. 
        apply Hadd in Hz as [Hz_g1 | [Hz_u | Hz_v]]; subst.
        + apply Hsubgraph in Hz_g1.
          erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
          erewrite (addEdge2_vvalid_iff y1 h u v e); eauto.
        + erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
          erewrite (addEdge2_vvalid_iff y1 h u v e); eauto.
        + erewrite <- (addEdge2_vvalid_iff i h x y a); eauto. 
          erewrite (addEdge2_vvalid_iff y1 h u v e); eauto.
      }
      {
        intros z w b Hstep_g2.
        destruct Hadd as [_ _ Hstep_g2_iff].
        apply Hstep_g2_iff in Hstep_g2 as [Hstep_g1 | [Hb [[Hz Hw] | [Hz Hw]]]].
        * assert (Hstep_y1 : step_aux y1 b z w) by (apply Hsubgraph; auto).
          assert (Hstep_h : step_aux h b z w) by (eapply addEdge2_old_step with (g1:=y1); eauto).
          destruct (classic (b = a)) as [Hba | Hba]; 
          [|eapply addEdge2_keep_step; eauto].
          subst; exfalso.
          eapply step_aux_unique_undirected in Hstep as [[] | []]; eauto; subst; 
          apply Hy; [eapply step_vvalid2; eauto | eapply step_vvalid1; eauto].
        * subst b z w.
          assert (Hstep_h : step_aux h e u v) by (eapply addEdge2_new_step_uv; eauto).
          eapply addEdge2_keep_step; eauto; symmetry; tauto.
        * subst b z w.
          assert (Hstep_h : step_aux h e v u) by (eapply addEdge2_new_step_vu; eauto).
          eapply addEdge2_keep_step; eauto.
          intro Heq; subst; apply Hin; auto. 
      }
Qed.


End prim.
