Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted subgraph path path_basic epath Zweight.
From GraphLib.examples Require Import prim.
From GraphLib.undirected Require Import tree.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.

Local Open Scope sets.
Local Open Scope Z.

Section kruskal.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}
        {addEdgeExist: addEdgeExist G V E}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.

Context (r: G)
        {r_valid: gvalid r}
        {ew: EdgeWeight G E}.


Lemma addEdge0_epath_new_to_old: 
  forall g h u v x y e p, 
    addEdge g h u v e -> 
    valid_epath h x p y -> 
    (~ In e p) ->
    valid_epath g x p y. 
Proof.
  intros g h u v x y e p Hadd Hvalid Hnotin. 
  revert x y Hvalid.
  induction p; intros. 
  - apply valid_epath_nil_inv in Hvalid; subst; auto. 
    apply valid_epath_empty; auto. 
  - apply valid_epath_cons_inv in Hvalid as [z [He1 He2]]. 
    eapply valid_epath_cons with (v:=z); eauto. 
    + apply Hadd in He1 as [|[? [[]|[]]]]; subst; auto. 
      * exfalso; apply Hnotin; left; auto. 
      * exfalso; apply Hnotin; left; auto. 
    + apply IHp; auto. 
      intros Hein; apply Hnotin; right; auto.
Qed.

Theorem kruskal_step: 
  forall g1 g2 u v e, 
    gvalid g1 /\ (forall u, ~ exists p, is_simple_epath g1 u p u /\ p <> nil) /\ (exists y1, is_mst r y1 /\ subgraph2 g1 y1) -> 
    step_aux r e u v -> 
    addEdge g1 g2 u v e -> 
    min_object_of_subset Z_op_le (fun e => forall u v, step_aux r e u v -> ~ reachable g1 u v) (weight r) e ->
    (forall u, ~ exists p, is_simple_epath g2 u p u /\ p <> nil) /\ (exists y2, is_mst r y2 /\ subgraph2 g2 y2).
Proof.
  intros g1 g2 u v e [Hvalid1 [Hno_circuit [y1 [Hmst1 Hsubgraph1]]]] Hstepr Hadd Hmin. 
  split. 
  (* 新图无环 *)
  1:{ 
    intros  w [p [Hsimple Hnotnil]]. 
    destruct Hmin as [? _]. 
    destruct (classic (In e p)) as [Hein | Hnotin]. 
    - apply in_split in Hein as [p1 [p2 Heq]]. 
      subst; clear Hnotnil.  
      destruct Hsimple as [Hpath Hnodup]. 
      apply valid_epath_app_inv in Hpath as [x [Hpre Hrest]]. 
      apply valid_epath_cons_inv in Hrest as [y [Hmid Hpost]]. 
      assert (step_aux r e x y). {
        apply Hadd in Hmid as [|[? [[]|[]]]]; subst; auto. 
        + apply Hmst1; apply Hsubgraph1; auto. 
        + apply step_sym; auto.
      } 
      eapply step_aux_unique_undirected in Hstepr as [[]|[]]; eauto; subst x y. 
      + eapply H; eauto. 
        eapply valid_epath_reachable. 
        instantiate (1:= (rev p1) ++ (rev p2)). 
        eapply valid_epath_app with (v:=w); auto. 
        * apply valid_epath_rev. 
          eapply addEdge0_epath_new_to_old; eauto. 
          apply NoDup_remove_2 in Hnodup. 
          rewrite in_app_iff in Hnodup. 
          tauto. 
        * apply valid_epath_rev. 
          eapply addEdge0_epath_new_to_old; eauto. 
          apply NoDup_remove_2 in Hnodup. 
          rewrite in_app_iff in Hnodup. 
          tauto. 
      + eapply H; eauto. 
        eapply valid_epath_reachable. 
        instantiate (1:= (rev p1) ++ (rev p2)). 
        eapply valid_epath_app with (v:=w); auto. 
        * apply valid_epath_rev. 
          eapply addEdge0_epath_new_to_old; eauto. 
          apply NoDup_remove_2 in Hnodup. 
          rewrite in_app_iff in Hnodup. 
          tauto. 
        * apply valid_epath_rev. 
          eapply addEdge0_epath_new_to_old; eauto. 
          apply NoDup_remove_2 in Hnodup. 
          rewrite in_app_iff in Hnodup. 
          tauto. 
    - eapply (Hno_circuit w). 
      destruct Hsimple. 
      exists p; split; auto. 
      split; auto. 
      eapply addEdge0_epath_new_to_old; eauto. 
  } 
  (* 新图包含在一个最小生成树里面 *)
  destruct (classic (evalid y1 e)) as [Hein | Hnotin].
  - exists y1; split; auto. 
    split.
    { 
      intros x Hx. 
      apply Hadd in Hx as [|[|]]; subst. 
      + apply Hsubgraph1; auto. 
      + apply Hmst1. 
        eapply step_vvalid1; eauto.
      + apply Hmst1. 
        eapply step_vvalid2; eauto.  
    } 
    {
      intros x y a Hstep.
      destruct Hadd as [Hvvalid Hevalid Hstep_aux].
      apply Hstep_aux in Hstep as [Hold | [Heq [[Hx Hy] | [Hx Hy]]]]; subst.
      + apply Hsubgraph1; auto.
      + eapply mst_edge_step with (r:=r); eauto.
      + apply step_sym. eapply mst_edge_step with (r:=r); eauto.
    } 
  - (* 当新增加的边e不在原来的被包含在的最小生成树中时 *)
    (* 将这条边e增加到最小生成树y1中去，y1 + e = h *)
    assert (Huy1: vvalid y1 u) by (apply Hmst1; eapply step_vvalid1; eauto).
    assert (Hvy1: vvalid y1 v) by (apply Hmst1; eapply step_vvalid2; eauto). 
    assert (exists h, gvalid h /\ addEdge y1 h u v e) as [h [Hvalid Hadd2]].
    {
      apply addEdge_valid; auto. 
      apply Hmst1.
    } 
    (* 则 h 中有一个简单回路 p ，包含边e *)
    assert (exists p, is_simple_epath h u p u /\ In e p /\ p <> nil) as [p [Hp [Heinp Hpne]]]. 
    {
      eapply tree_addEdge_have_circuit.
      6: apply Hadd2. 
      all: try apply Hmst1; try auto.
      eapply step_vvalid1; eauto. 
      eapply step_vvalid2; eauto. 
    }
    (* p 中包含一条跨越 g1 当前连通分量的旧树边 a *)
    assert (exists x y a, reachable g1 u x /\ ~ reachable g1 u y /\ step_aux h a x y /\ In a p /\ a <> e) as [x [y [a [Hx [Hy [Hstep_ah [Hinap Hane]]]]]]].
    {
      pose proof Hmin as [Hmin_in _].
      assert (Hnot_reach_uv : ~ reachable g1 u v) by (eapply Hmin_in; eauto). 
      eapply addEdge2_cycle_without_new_edge_simple in Hp
      as [q [[Hqpath Hqnodup] Hqmem]]; eauto.
      eapply valid_epath_cross with (P := fun z => reachable g1 u z) in Hqpath
        as [x [y [a [Hx [Hy [Hstep_y1 Hinaq]]]]]]; eauto.
      apply Hqmem in Hinaq as [Hinap Hane].
      exists x, y, a. repeat split; auto.
      eapply addEdge2_old_step; eauto. 
      reflexivity.
    }   
    (* 将 a 从 h 中删除 *)
    assert (exists i, gvalid i /\ addEdge i h x y a /\ (vvalid i x /\ vvalid i y /\ ~ evalid i a)) 
    as [i [Hvalidi [Hi [Hvx [Hvy Hnotina]]]]]. {
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
    + eapply (addEdge2_delete_circuit_tree y1 h i u v e x y a p); eauto. 
      all: try tauto. 
      all: apply Hmst1.

    (* i 是 原图的子图 *)
    + destruct Hmst1 as [Hy1_legal Hy1_min].
      destruct Hy1_legal as [_ [_ Hsubeq_y1]].
      destruct Hsubeq_y1 as [Hy1_vertex Hy1_step].
      split.
      * intros z.
        rewrite <- Hy1_vertex.
        rewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
        apply addEdge2_vvalid_iff with (u := u) (v := v) (e := e); auto.
      * intros z w b Hstep_i.
        eapply addEdge2_old_step in Hstep_i as Hstep_h; try apply Hi; eauto.
        destruct Hadd2 as [_ _ Hstep_h_iff].
        apply Hstep_h_iff in Hstep_h as [Hstep_y1 | [Hb [[] | []]]]; subst; auto.
        apply step_sym; auto. 

    (* i 的权值小于等于 h 的权值 *)
    + intros b Hb.
      eapply Z_op_le_trans with (y:= total_weight r y1); 
      [|apply Hmst1; auto]. 
      pose proof Hadd2 as Hadd2'. 
      pose proof Hi as Hi'. 

      apply addEdge2_elist_permutation in Hadd2; auto. 
      2:{ apply Hmst1. } 

      apply addEdge2_elist_permutation in Hi; auto.

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
        unfold sumE in H. 
        rewrite H.
        simpl; reflexivity.
      }
      assert (Hh_i : total_weight r h = Z_op_plus (weight r a) (total_weight r i)).
      {
        unfold total_weight.
        pose proof (Hperm_sum _ _ Hi). 
        unfold sumE in H. 
        rewrite H.
        simpl; reflexivity.
      }
      destruct Hmst1 as [[Hy1_valid [_ Hsubeq_y1]] _].
      destruct Hsubeq_y1 as [_ Hy1_step].
      assert (Hstep_y1 : step_aux y1 a x y) by (eapply addEdge2_keep_step; eauto; tauto).
      assert (Hin_a_y1 : In a (bijective_listE y1)).
      { apply bijective_edges; auto. eapply step_evalid; eauto. }
      assert (Hwea : Z_op_le (weight r e) (weight r a)).
      {
        destruct Hmin as [_ Hmin_sound].
        apply Hmin_sound.
        intros s t Hstep_ra Hreach_st.
        assert (Hstep_ra_xy : step_aux r a x y) by (apply Hy1_step; auto).
        eapply step_aux_unique_undirected in Hstep_ra as [[Hs Ht] | [Hs Ht]]; eauto; subst.
        - apply Hy. eapply reachable_trans; eauto.
        - apply Hy. eapply reachable_trans; [apply Hx|].
          destruct (reachable_valid_epath g1 y t Hreach_st) as [q Hq].
          eapply valid_epath_reachable.
          apply valid_epath_rev; eauto.
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
	        destruct Hadd as [Hvvalid_g2 _ _].
	        apply Hvvalid_g2 in Hz as [|[|]]; subst.
	        + apply Hsubgraph1 in H. 
	          apply (addEdge2_vvalid_iff i h x y a); eauto.
	          apply (addEdge2_vvalid_iff y1 h u v e); auto.
	        + apply (addEdge2_vvalid_iff i h x y a); auto.
	          apply (addEdge2_vvalid_iff y1 h u v e); auto.
	        + apply (addEdge2_vvalid_iff i h x y a); eauto.
	          apply (addEdge2_vvalid_iff y1 h u v e); auto.
	      }
	      {
	        intros z w b Hstep_g2.
	        destruct Hadd as [_ _ Hstep_g2_iff].
	        apply Hstep_g2_iff in Hstep_g2 as [Hstep_g1 | [Hb [[Hz Hw] | [Hz Hw]]]].
	        * assert (Hstep_y1_b : step_aux y1 b z w) by (apply Hsubgraph1; auto).
	          assert (Hstep_h_b : step_aux h b z w) by (eapply addEdge2_old_step with (g1:=y1); eauto).
	          destruct (classic (b = a)) as [Hba | Hba].
	          + subst b. exfalso.
	            eapply step_aux_unique_undirected in Hstep_ah as [[]|[]]; eauto; subst; 
              apply Hy; eapply reachable_step_reachable; eauto; 
              exists a; [|apply step_sym]; auto.
	          + eapply addEdge2_keep_step; eauto.
	        * subst b z w.
	          assert (Hstep_h : step_aux h e u v) by (eapply addEdge2_new_step_uv; eauto).
	          eapply addEdge2_keep_step; eauto; symmetry; tauto.
	        * subst b z w.
	          assert (Hstep_h : step_aux h e v u) by (eapply addEdge2_new_step_vu; eauto).
	          eapply addEdge2_keep_step; eauto.
	      }
Qed.

End kruskal.
