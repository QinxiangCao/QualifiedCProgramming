Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted subgraph path path_basic vpath epath Zweight.
From GraphLib.examples Require Import prim.
From GraphLib.undirected Require Import tree.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import General.NoDup.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.


Class emptyGraph (G V E: Type) (src: V) {pg: Graph G V E} {gv: GValid G} := {
  empty_graph: G;
  empty_graph_valid: gvalid empty_graph;
  empty_graph_vvalid: forall v, vvalid empty_graph v <-> v = src;
  empty_graph_evalid: forall e, evalid empty_graph e <-> False;
}. 

Section Prim.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noempty: NoEmptyEdge G V E}
        {undirected: UndirectedGraph G V E}
        {stepunique: StepUniqueUndirected G V E}
        (* {simplegraph: SimpleGraph G V E} *)
        {finitegraph: FiniteGraph G V E}
        {elistbijective: EListBijective G V E}
        (g: G).

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        
        {tr: Tree G V E P}.

Context {ew: EdgeWeight G E}.

Context (g_connected: connected g).


Record St: Type := mkSt_s {
  graph_in_state: G;
}.

Context (src: V)
        (validsrc: vvalid g src)
        (g_valid: gvalid g)
        {add_edge_in_subgraph: addEdgeInSubgraph G V E}
        {addEdgeGValid: addEdgeGValid G V E}
        {emptyGraph: emptyGraph G V E src}.

Lemma spanningtree_exist_in_subgraph:
  exists h,
    gvalid h /\ tree h /\ subgraph_vertex_eq h g.
Proof.
  destruct (connected_subgraph_eq_exist g (g_valid:=g_valid) (g_connected:=g_connected))
    as [h [[Hvalid [Hconnected Hsub]] Hmin]].
  exists h; split; [|split]; auto.
  apply tree_decide; auto.
  intros [u [p [Hpne Hsimple]]].
  destruct p; [auto|clear Hpne].
  pose proof Hsimple as [Hpath Hnodup].
  apply valid_epath_cons_inv in Hpath as [v [Hstep Hrest]].
  pose proof Hvalid as Hh.
  assert (Hhsubg: subgraph2 h g).
  {
    destruct Hsub as [Hsubv Hsubs].
    split.
    - intros z Hz. apply Hsubv; auto.
    - intros z w b Hstep'. apply Hsubs; auto.
  }
  assert (Hex_remove:
    exists i,
      gvalid i /\
      addEdge i h u v e /\
      subgraph2 i g /\
      vvalid i u /\
      vvalid i v /\
      ~ evalid i e).
  {
    eapply remove_edge_in_subgraph; eauto.
    - eapply step_vvalid1; eauto.
    - eapply step_vvalid2; eauto.
    - eapply step_evalid; eauto.
  }
  destruct Hex_remove as [i [Hvalidi [Hadd [Hsubi [Hvx [Hvy Hnotinea]]]]]].
  assert (connected_subgraph_eq g i). {
      split; [|split]; auto.
      + intros x y Hx Hy.
        assert (Hhx:vvalid h x) by (eapply Hadd; auto).
        assert (Hhy:vvalid h y) by (eapply Hadd; auto).
        pose proof Hconnected x y Hhx Hhy.
        apply reachable_valid_epath in H as [q Hqpath].
        apply valid_epath_simple in Hqpath as [q' [Hqpath Hqnodup]].
        2:{ intros; eapply step_aux_unique_undirected with (g:=h); try apply Hh; eauto. }
        clear q; rename q' into q.
        destruct (classic (In e q)) as [Hin | Hnotin]; [|].
        * apply in_split in Hin as [q1 [q2 Hp]]; subst.
          apply valid_epath_app_inv in Hqpath as [a [Hqpre Hqrest]].
          apply valid_epath_cons_inv in Hqrest as [b [Hqstep Hqpost]].
          eapply step_aux_unique_undirected in Hstep as [[]|[]]; eauto; subst a b.
          -- eapply valid_epath_reachable.
             instantiate (1:= q1 ++ (rev p) ++ q2).
             eapply addEdge2_valid_epath_new_to_old; eauto.
             {
               eapply valid_epath_app; eauto.
               eapply valid_epath_app; eauto.
               apply valid_epath_rev; auto.
             }
             {
               rewrite ! in_app_iff; intros ?.
               apply NoDup_remove_2 in Hqnodup; rewrite in_app_iff in Hqnodup.
               inversion Hnodup; subst.
               rewrite <- in_rev in H.
               tauto.
             }
          -- eapply valid_epath_reachable.
             instantiate (1:= q1 ++ p ++ q2).
             eapply addEdge2_valid_epath_new_to_old; eauto.
             {
               eapply valid_epath_app; eauto.
               eapply valid_epath_app; eauto.
             }
             {
               rewrite ! in_app_iff; intros ?.
               apply NoDup_remove_2 in Hqnodup; rewrite in_app_iff in Hqnodup.
               inversion Hnodup; subst.
               tauto.
             }
        * eapply valid_epath_reachable.
          eapply addEdge2_valid_epath_new_to_old; eauto.
      + split.
        * intros; split; intros.
          -- apply Hsubi; auto.
          -- apply Hsub in H.
             apply Hadd in H as [|[|]]; auto; subst; auto.
        * intros.
          apply Hsubi; auto.
    }
    assert (Hadd_perm: Permutation (bijective_listE h) (e :: bijective_listE i)).
    {
      eapply addEdge_elist_permutation with
        (g1 := i) (g2 := h) (u := u) (v := v) (e := e); eauto.
      - apply bijective_listE_NoDup. exact Hvalidi.
      - apply bijective_edges. exact Hvalidi.
      - apply bijective_listE_NoDup. exact Hh.
      - apply bijective_edges. exact Hh.
    }
    apply Permutation_length in Hadd_perm.
    apply Hmin in H; unfold edge_num in H.
    rewrite ! Zlength_correct in H.
    simpl in Hadd_perm.
    lia.
Qed.

Theorem connected_have_mst_in_subgraph:
  exists h, is_mst g h.
Proof.
  set (edge_weight_sum := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
  set (legal := fun h => gvalid h /\ tree h /\ subgraph_vertex_eq h g).
  assert (edge_weight_sum_perm:
    forall l1 l2, Permutation l1 l2 -> edge_weight_sum l1 = edge_weight_sum l2).
  {
    intros l1 l2 Hperm.
    induction Hperm; unfold edge_weight_sum in *; simpl; auto.
    - rewrite IHHperm; auto.
    - destruct (weight g x), (weight g y), (fold_right Z_op_plus (Some 0%Z) (map (weight g) l)); simpl; auto; f_equal; lia.
    - congruence.
  }
  destruct (Nodup_all_sublists (bijective_listE g) (bijective_listE_NoDup g g_valid))
    as [edge_sets [Hedge_sets_sound Hedge_sets_complete]].
  set (represented := fun l =>
    In l edge_sets /\ exists h, legal h /\ Permutation l (bijective_listE h)).

  assert (legal_edges_in_g:
    forall h, legal h -> incl (bijective_listE h) (bijective_listE g)).
  {
    intros h [Hvalid [_ Hsub]] e Hin.
    apply bijective_edges in Hin; auto.
    apply no_empty_edge in Hin as [u [v Hstep]]; auto.
    apply bijective_edges; auto.
    eapply step_evalid; eauto.
    apply Hsub; eauto.
  }
  destruct spanningtree_exist_in_subgraph as [h0 Hh0].
  assert (represented_exists : exists l, In l edge_sets /\ represented l).
  {
    destruct (Hedge_sets_complete (bijective_listE h0)) as [l0 [Hl0 Hperm0]].
    - apply bijective_listE_NoDup; tauto.
    - apply legal_edges_in_g; auto.
    - exists l0; split; auto.
      split; auto; exists h0; split; auto.
  }
  destruct represented_exists as [l0 [Hl0 Hrepr0]].
  destruct (Z_op_finite_min edge_weight_sum represented edge_sets l0 Hl0 Hrepr0
    ltac:(intros y Hy; exact (proj1 Hy))) as [lm [Hreprm Hminm]].
  destruct Hreprm as [_ [hm [Hlegalm Hpermm]]].
  exists hm.
  split; auto.
  intros h Hlegalh.
  destruct (Hedge_sets_complete (bijective_listE h)) as [lh [Hlh Hpermh]].
  - apply bijective_listE_NoDup; try tauto.
    apply Hlegalh.
  - apply legal_edges_in_g; auto.
  - assert (Hreprh : represented lh) by (split; auto; exists h; split; auto).
    specialize (Hminm lh Hreprh).
    pose proof (edge_weight_sum_perm lm (bijective_listE hm) Hpermm).
    unfold edge_weight_sum in H.
    unfold total_weight.
    rewrite <- H.
    rewrite (edge_weight_sum_perm lh (bijective_listE h) Hpermh) in Hminm.
    exact Hminm.
Qed.

Lemma prim_step_in_subgraph:
  forall g1 g2 u v e,
    gvalid g1 /\ tree g1 /\ (exists y1, is_mst g y1 /\ subgraph2 g1 y1) ->
    step_aux g e u v ->
    vvalid g1 u -> ~ vvalid g1 v ->
    addEdge g1 g2 u v e ->
    min_object_of_subset Z_op_le
      (fun e => exists u v, vvalid g1 u /\ ~ vvalid g1 v /\ step_aux g e u v)
      (weight g) e ->
    exists y2, is_mst g y2 /\ subgraph2 g2 y2.
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
      + eapply mst_edge_step with (r:=g); eauto.
      + apply step_sym. eapply mst_edge_step with (r:=g); eauto.
    }
  - assert (Huy1: vvalid y1 u) by (apply Hsubgraph; auto).
    assert (Hvy1: vvalid y1 v) by (apply Hmst; eapply step_vvalid2; eauto). 
    assert (Hy1subg: subgraph2 y1 g).
    {
      split.
      - intros z Hz. apply Hmst; auto.
      - intros z w b Hstep. apply Hmst; auto.
    }
    assert (exists h, gvalid h /\ addEdge y1 h u v e /\ subgraph2 h g) as [h [Hvalid [Hadd2 Hsubh]]].
    {
      eapply add_original_edge_in_subgraph; eauto.
      - apply Hmst.
    } 
    assert (exists p, is_simple_epath h u p u /\ In e p /\ p <> nil) as [p [Hp [Heinp Hpne]]]. 
    {
      eapply tree_addEdge_have_circuit. 
      6: apply Hadd2. 
      all: try apply Hmst; try auto. 
      eapply step_vvalid1; eauto. 
      eapply step_vvalid2; eauto. 
    } 
    assert (exists x y a, vvalid g1 x /\ ~ vvalid g1 y /\ step_aux h a x y /\ In a p /\ a <> e) as [x [y [a [Hx [Hy [Hstep Hin]]]]]].
    {
      eapply circuit_have_pair_cross_edge with (v := v); eauto; 
      try (try destruct Hadd; tauto). 
      destruct Hadd2 as [_ _ Hstep_aux]. 
      apply Hstep_aux; right; auto.
    }
    assert (exists i, gvalid i /\ addEdge i h x y a /\ subgraph2 i g /\ (vvalid i x /\ vvalid i y /\ ~ evalid i a)) as [i [Hvalidi [Hi [Hsubi [Hvx [Hvy Hnotina]]]]]]. {
      eapply remove_edge_in_subgraph; eauto.
      - eapply step_vvalid1; eauto.
      - eapply step_vvalid2; eauto.
      - eapply step_evalid; eauto.
    }
    assert (Hvalid_y1: gvalid y1) by (apply Hmst). 
    assert (Htree_i: tree i). 
    {
      eapply addEdge2_delete_circuit_tree
        with (y1:=y1) (h:=h) (u:=u) (v:=v) (e:=e)
             (x:=x) (y:=y) (a:=a) (p:=p); eauto.
      all: try apply Hmst; try tauto; try (repeat split; auto).
    }
    exists i; split.
    + split; [split; [|split]|].
      * exact Hvalidi.
      * exact Htree_i.
      * destruct Hmst as [Hy1_legal Hy1_min].
        destruct Hy1_legal as [_ [_ Hsubeq_y1]].
        destruct Hsubeq_y1 as [Hy1_vertex Hy1_step].
        split.
        -- intros z.
           rewrite <- Hy1_vertex.
           erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
           apply addEdge2_vvalid_iff with (u := u) (v := v) (e := e); auto.
        -- intros z w b Hstep_i.
           eapply addEdge2_old_step in Hstep_i as Hstep_h; try apply Hi; eauto.
           destruct Hadd2 as [_ _ Hstep_h_iff].
           apply Hstep_h_iff in Hstep_h as [Hstep_y1 | [Hb [[] | []]]]; subst; auto.
           apply step_sym; auto.
      * intros b Hb.
        eapply Z_op_le_trans with (y:= total_weight g y1);
        [|apply Hmst; auto].
        pose proof Hadd2 as Hadd2'.
        pose proof Hi as Hi'.
        assert (Hadd2_perm: Permutation (bijective_listE h) (e :: bijective_listE y1)).
        {
          eapply addEdge_elist_permutation with
            (g1 := y1) (g2 := h) (u := u) (v := v) (e := e); eauto.
          - apply bijective_listE_NoDup. exact Hvalid_y1.
          - apply bijective_edges. exact Hvalid_y1.
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
        set (sumE := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
        assert (Hperm_sum : forall l1 l2, Permutation l1 l2 -> sumE l1 = sumE l2).
        {
          intros l1 l2 Hperm.
          induction Hperm; subst sumE; simpl; auto.
          - rewrite IHHperm; auto.
          - rewrite !Z_op_plus_assoc.
            rewrite (Z_op_plus_comm (weight g x0) (weight g y0)).
            reflexivity.
          - rewrite IHHperm1, IHHperm2; auto.
        }
        assert (Hh_y1 : total_weight g h = Z_op_plus (weight g e) (total_weight g y1)).
        {
          unfold total_weight.
          pose proof (Hperm_sum _ _ Hadd2).
          unfold sumE in H0.
          simpl in H0.
          apply H0.
        }
        assert (Hh_i : total_weight g h = Z_op_plus (weight g a) (total_weight g i)).
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
        assert (Hwea : Z_op_le (weight g e) (weight g a)).
        {
          destruct Hmin as [_ Hmin_sound].
          apply Hmin_sound.
          exists x, y.
          repeat split; auto.
        }
        assert (Hnone_in_sum :
          forall l, In a l -> weight g a = None -> sumE l = None).
        {
          intros l.
          induction l as [|c l IH]; intros Hinc Hwa; simpl in *; [contradiction|].
          destruct Hinc as [Hc | Hinc].
          - subst. unfold sumE; simpl. rewrite Hwa. reflexivity.
          - apply IH in Hwa; auto. unfold sumE; simpl.
            unfold sumE in Hwa; simpl in Hwa.
            rewrite Hwa. apply Z_op_plus_none_r.
        }
        destruct (weight g a) as [wa|] eqn:Hwa.
        -- destruct (weight g e) as [we|] eqn:Hwe; simpl in Hwea; [|contradiction].
           rewrite Hh_y1 in Hh_i.
           destruct (total_weight g i) as [wi|] eqn:Hwi;
           destruct (total_weight g y1) as [wy|] eqn:Hwy;
           simpl in *; try discriminate; auto.
           inversion Hh_i; subst; lia.
        -- assert (Hy1_none : total_weight g y1 = None).
           {
             unfold total_weight.
             apply Hnone_in_sum; auto.
           }
           rewrite Hy1_none.
           apply Z_op_le_none_r.
    + split.
      * intros z Hz.
        apply Hadd in Hz as [Hz_g1 | [Hz_u | Hz_v]]; subst.
        -- apply Hsubgraph in Hz_g1.
           erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
           erewrite (addEdge2_vvalid_iff y1 h u v e); eauto.
        -- erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
           erewrite (addEdge2_vvalid_iff y1 h u v e); eauto.
        -- erewrite <- (addEdge2_vvalid_iff i h x y a); eauto.
           erewrite (addEdge2_vvalid_iff y1 h u v e); eauto.
      * intros z w b Hstep_g2.
        destruct Hadd as [_ _ Hstep_g2_iff].
        apply Hstep_g2_iff in Hstep_g2 as [Hstep_g1 | [Hb [[Hz Hw] | [Hz Hw]]]].
        -- assert (Hstep_y1 : step_aux y1 b z w) by (apply Hsubgraph; auto).
           assert (Hstep_h : step_aux h b z w) by (eapply addEdge2_old_step with (g1:=y1); eauto).
           destruct (classic (b = a)) as [Hba | Hba];
           [|eapply addEdge2_keep_step; eauto].
           subst; exfalso.
           eapply step_aux_unique_undirected in Hstep as [[] | []]; eauto; subst;
           apply Hy; [eapply step_vvalid2; eauto | eapply step_vvalid1; eauto].
        -- subst b z w.
           assert (Hstep_h : step_aux h e u v) by (eapply addEdge2_new_step_uv; eauto).
           eapply addEdge2_keep_step; eauto; symmetry; tauto.
        -- subst b z w.
           assert (Hstep_h : step_aux h e v u) by (eapply addEdge2_new_step_vu; eauto).
           eapply addEdge2_keep_step; eauto.
           intro Heq; subst; apply Hin; auto.
Qed.

Definition initSt: St := {|
  graph_in_state := empty_graph;
|}.

Instance: Settable St := settable! mkSt_s <graph_in_state>.

Definition is_cut_edge (s: St) (e: E): Prop :=
  exists u v, 
  vvalid s.(graph_in_state) u /\ ~ vvalid s.(graph_in_state) v /\ step_aux g e u v.

Definition get_min_cut_edge (f: St -> E -> Prop): program St E :=
  get (fun s e => min_object_of_subset Z_op_le (fun e => is_cut_edge s e) (weight g) e).

Definition add_to_mst (u v: V) (e: E): program St unit :=
  update (fun s1 s2: St => addEdge (s1.(graph_in_state)) (s2.(graph_in_state)) u v e).

Definition Prim_body: program St unit :=
  e <- get_min_cut_edge is_cut_edge ;;
  x <- get (fun s '(u, v) => vvalid s.(graph_in_state) u /\ ~ vvalid s.(graph_in_state) v /\ step_aux g e u v);;
  add_to_mst (fst x) (snd x) e.

Definition Prim: program St unit :=
  whileP (fun s => exists e, is_cut_edge s e) 
    Prim_body.      

Definition Prim2: program St unit := 
  range_iter 0 (Zlength (bijective_listV g) - 1) (fun _ _ => Prim_body) tt.


Lemma state_to_tree_init: tree (empty_graph).
Proof. 
  apply tree_decide. 
  - intros x y Hx Hy. 
    rewrite ! empty_graph_vvalid in Hx, Hy; 
    simpl in Hx, Hy;
    sets_unfold in Hx; sets_unfold in Hy; subst. 
    reflexivity. 
  - intros [u [p [? []]]]. 
    destruct p; auto. 
    apply valid_epath_cons_inv in H0 as [v [Hstep _]]. 
    apply step_evalid in Hstep. 
    rewrite empty_graph_evalid in Hstep; auto. 
Qed.

(* Prim算法的正确性 *)
Theorem Prim_correct: 
  Hoare (fun s => s = initSt) 
        Prim 
        (fun _ s => is_mst g (s.(graph_in_state))).
Proof. 
  eapply Hoare_conseq. 
  3:{ 
    unfold Prim. 
    eapply Hoare_whileP with (P := fun s => (tree (s.(graph_in_state)) /\ 
    (exists y, is_mst g y /\ subgraph2 (s.(graph_in_state)) y)) /\ gvalid (s.(graph_in_state)) /\ vvalid (s.(graph_in_state)) src). 
    intro_state. 
    unfold Prim_body. 
    unfold get_min_cut_edge, add_to_mst.
    hoare_auto_s. 
    destruct H as [Hx [[Htree Hmst] [Hgvalid Hsrc]]]. 
    destruct a0 as (u, v). 
    destruct H1 as [Hu [Hv Hstepg]]. 
    rename a into e; simpl in *. 
    assert ((exists y : G, is_mst g y /\ subgraph2 (graph_in_state s) y)) by (eapply prim_step_in_subgraph; eauto).
    split; [split|]; auto. 
    assert (~ evalid (graph_in_state s0) e).  
    {
      intros He. 
      eapply no_empty_edge in He as [x [y Hstep]]; auto. 
      destruct H as [y' [Hmst' Hsub']]. 
      destruct H2 as [_ _ H2].
      
      assert (step_aux (graph_in_state s) e x y) by (apply H2; auto). 
      destruct Hmst' as [[Hmst' [Htree' Hsubeq]] Hmin']. 
      apply Hsub' in H. 
      apply Hsubeq in H. 
      eapply step_aux_unique_undirected in Hstepg as [[] | []]; eauto; subst; auto; 
      apply Hv; [eapply step_vvalid2|eapply step_vvalid1]; eauto.
    }
    eapply addEdge_tree; eauto. 
    split; [|apply H2; left; auto]. 
    eapply addEdge_gvalid; [|apply H2].  
    all: try tauto. 
  }
  {
    intros; subst; split; [split|split].
    + apply state_to_tree_init. 
    + destruct connected_have_mst_in_subgraph as [y Hy].
      exists y. split; auto. 
      split. 
      {
        intros x Hx. 
        apply empty_graph_vvalid in Hx; subst. 
        apply Hy; auto.
      }
      { 
        intros u v e Hstep. 
        exfalso; eapply step_evalid in Hstep. 
        apply empty_graph_evalid in Hstep; auto. 
      } 
    + apply empty_graph_valid. 
    + apply empty_graph_vvalid; reflexivity. 
  }
  { 
    simpl; intros _ s [[[] [Hgvalid Hsrc]]]. 
    destruct H0 as [y [Hismst Hsub]]. 
    assert (Hsubeq: subgraph_vertex_eq (s.(graph_in_state)) g).
    {
      split. 
      * intros x; split; intros Hx. 
        {
          apply Hismst. 
          apply Hsub; auto.
        } 
        {
          apply NNPP; intros Hx'. 
          apply H1. 
          pose proof g_connected src x validsrc Hx. 
          apply reachable_valid_epath in H0 as [p Hp]. 
          eapply valid_epath_cross with (P:= vvalid (s.(graph_in_state))) in Hp; auto. 
          destruct Hp as [u [v [e [? [? []]]]]]; try rewrite state_to_tree_vvalid in *. 
          exists e, u, v; repeat split; auto; tauto.
        }
      * intros; apply Hismst. 
        apply Hsub; auto.
    }
    split; [split; [|split]|]; auto.
    intros q Hq. 
    destruct Hismst as [Hismst Hmin]. 
    pose proof Hq as Hq'. 
    apply Hmin in Hq. 
    set (sumE := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
    assert (Hperm_sum : forall l1 l2, Permutation l1 l2 -> sumE l1 = sumE l2).
    {
      intros l1 l2 Hperm.
      induction Hperm; subst sumE; simpl; auto.
      - rewrite IHHperm; auto.
      - rewrite !Z_op_plus_assoc.
        rewrite (Z_op_plus_comm (weight g x) (weight g y0)).
        reflexivity.
      - rewrite IHHperm1, IHHperm2; auto.
    } 
    eapply Z_op_le_trans; eauto.
    assert (Permutation (bijective_listE (s.(graph_in_state))) (bijective_listE y)). 
    {
      apply NoDup_Permutation; try apply bijective_listE_NoDup;
      [apply Hgvalid | apply Hismst | ]; auto. 
      intros e; rewrite ! bijective_edges; 
      [| apply Hismst| apply Hgvalid]; auto. 
      split; intros He. 
      - apply no_empty_edge in He as [u [v Hstep]]; [|apply Hgvalid]. 
        apply Hsub in Hstep. 
        eapply step_evalid; eauto. 
      - apply no_empty_edge in He as [u [v Hstep]]; [|apply Hismst]. 
        assert (Hu: vvalid s.(graph_in_state) u) by (apply Hsubeq; apply Hismst; eapply step_vvalid1; eauto). 
        assert (Hv: vvalid s.(graph_in_state) v) by (apply Hsubeq; apply Hismst; eapply step_vvalid2; eauto). 
        apply NNPP; intros He. 
        pose proof H as H'.
        apply tree_connected in H. 
        pose proof H u v Hu Hv. 
        apply reachable_valid_epath in H0 as [p Hp]. 
        assert (~ In e p). { 
          intros ?; apply He; apply in_split in H0 as [l1 [l2 H0]]; subst. 
          eapply valid_epath_app_inv in Hp as [w [Hpre Hrest]]; auto. 
          apply valid_epath_cons_inv in Hrest as [x [Hstep' _]]. 
          eapply step_evalid; eauto. 
        }
        eapply valid_epath_simple_Forall with (eset := fun a => ~ a = e) in Hp as [r [[Hrvalid Hrnodup] Hrfor]]. 
        2:{ intros; eapply step_aux_unique_undirected with (g:= (s.(graph_in_state))); eauto. } 
        2:{ rewrite Forall_forall in *. 
          intros x Hx ?; subst; auto. } 
        destruct Hismst as [_ [Htree _]]. 
        apply tree_no_curcuit in Htree. 
        apply Htree.
        exists u, (r ++ e :: nil); split; 
        [symmetry; apply app_cons_not_nil|]. 
        assert (Hpath: forall x l z, valid_epath (s.(graph_in_state)) x l z -> valid_epath y x l z). { 
            intros x l.
            revert x.
            induction l as [|a l IHl]; intros x z Hpath.
            - apply valid_epath_nil_inv in Hpath; subst.
              apply valid_epath_empty.
            - apply valid_epath_cons_inv in Hpath as [? []].
              eapply valid_epath_cons.
              + apply Hsub; exact H2.
              + apply IHl; auto.
        } apply Hpath in Hrvalid. 
        split. 
        + eapply valid_epath_snoc; eauto. 
          apply step_sym; auto. 
        + apply Nodup_app_comm. 
          simpl; constructor; auto. 
          rewrite Forall_forall in *; intros He'; 
          apply Hrfor in He'; auto. 
    } 
    unfold sumE in Hperm_sum. 
    apply Hperm_sum in H0. 
    unfold total_weight. 
    rewrite H0. 
    destruct ((fold_right Z_op_plus (Some 0) (map (weight g) (bijective_listE y)))); simpl; [lia|auto]. 
  } 

Qed.

(* 固定轮数版本 Prim2 的正确性：这是给 C refinement 使用的主定理。 *)
Theorem Prim2_correct:
  Hoare (fun s => s = initSt)
        Prim2
        (fun _ s => is_mst g (s.(graph_in_state))).
Proof.
  eapply Hoare_conseq.
  3:{
    unfold Prim2.
    eapply Hoare_range_iter' with (P := fun i _ s =>
      ((tree (s.(graph_in_state)) /\
        (exists y, is_mst g y /\ subgraph2 (s.(graph_in_state)) y)) /\
       gvalid (s.(graph_in_state)) /\
       vvalid (s.(graph_in_state)) src) /\
      Zlength (bijective_listV s.(graph_in_state)) = (i + 1)%Z).
    1:{
      assert (Hin : In src (bijective_listV g)) by (apply bijective_vertices; auto).
      destruct (bijective_listV g) as [|v vs]; simpl in *; [contradiction|].
      rewrite Zlength_cons.
      pose proof (Length.Zlength_nonneg vs); lia.
    }
    intros i _ [].
    intro_state.
    unfold Prim_body.
    unfold get_min_cut_edge, add_to_mst.
    hoare_auto_s.
    destruct H as [[[Htree Hmst] [Hgvalid Hsrc]] Hcount].
    rename H0 into Hmin.
    rename H1 into Hends.
    rename H2 into Hadd.
    destruct a0 as (u, v).
    destruct Hends as [Hu [Hv Hstepg]].
    rename a into e; simpl in *.
    assert (Hmst_new:
      exists y : G, is_mst g y /\ subgraph2 (graph_in_state s) y).
    { eapply prim_step_in_subgraph; eauto. }
    assert (He_new: ~ evalid (graph_in_state s0) e).
    {
      intros He.
      eapply no_empty_edge in He as [x [y Hstep]]; auto.
      destruct Hmst_new as [y' [Hmst' Hsub']].
      destruct Hadd as [_ _ Hadd_step].

      assert (step_aux (graph_in_state s) e x y) by (apply Hadd_step; auto).
      destruct Hmst' as [[Hmst' [Htree' Hsubeq]] Hmin'].
      apply Hsub' in H.
      apply Hsubeq in H.
      eapply step_aux_unique_undirected in Hstepg as [[] | []]; eauto; subst; auto;
      apply Hv; [eapply step_vvalid2|eapply step_vvalid1]; eauto.
    }
    assert (Htree_new: tree (graph_in_state s)) by (eapply addEdge_tree; eauto).
    assert (Hgvalid_new: gvalid (graph_in_state s)) by (eapply addEdge_gvalid; eauto).
    assert (Hsrc_new: vvalid (graph_in_state s) src) by (eapply addEdge_vvalid; eauto).
    assert (HpermV:
      Permutation (bijective_listV (graph_in_state s))
                  (v :: bijective_listV (graph_in_state s0))).
    {
      eapply (addEdge_vlist_permutation
        (graph_in_state s0) (graph_in_state s) u v e Hu Hv Hadd).
      * apply bijective_listV_NoDup; auto.
      * intros x; apply bijective_vertices; auto.
      * apply bijective_listV_NoDup; auto.
      * intros x; apply bijective_vertices; auto.
    }
    repeat split; auto.
    apply Permutation_length in HpermV.
    rewrite ! Zlength_correct in *.
    simpl in HpermV.
    lia.
  }
  {
    intros; subst; split.
    - split; [split|split].
      + apply state_to_tree_init.
      + destruct connected_have_mst_in_subgraph as [y Hy].
        exists y. split; auto.
        split.
        {
          intros x Hx.
          apply empty_graph_vvalid in Hx; subst.
          apply Hy; auto.
        }
        {
          intros u v e Hstep.
          exfalso; eapply step_evalid in Hstep.
          apply empty_graph_evalid in Hstep; auto.
        }
      + apply empty_graph_valid.
      + apply empty_graph_vvalid; reflexivity.
    - assert (HpermV:
        Permutation (bijective_listV empty_graph) (src :: nil)).
      {
        apply NoDup_Permutation.
        * apply bijective_listV_NoDup; apply empty_graph_valid.
        * constructor; [simpl; tauto | constructor].
        * intros x.
          rewrite bijective_vertices; [|apply empty_graph_valid].
          rewrite empty_graph_vvalid.
          simpl; intuition congruence.
      }
      apply Permutation_length in HpermV.
      rewrite Zlength_correct.
      simpl in *; lia.
  }
  {
    simpl; intros _ s [[[Htree Hmst] [Hgvalid Hsrc]] Hcount].
    destruct Hmst as [y [Hismst Hsub]].
    assert (Hsubeq: subgraph_vertex_eq (s.(graph_in_state)) g).
    {
      assert (Hincl:
        incl (bijective_listV (s.(graph_in_state))) (bijective_listV g)).
      {
        intros x Hx.
        apply bijective_vertices; [apply g_valid|].
        apply Hismst; apply Hsub.
        apply bijective_vertices in Hx; auto.
      }
      assert (Hlen:
        length (bijective_listV (s.(graph_in_state))) =
        length (bijective_listV g)).
      {
        assert (HZlen:
          Zlength (bijective_listV (s.(graph_in_state))) =
          Zlength (bijective_listV g)) by lia.
        rewrite ! Zlength_correct in HZlen.
        now apply Nat2Z.inj in HZlen.
      }
      assert (Hincl_rev:
        incl (bijective_listV g) (bijective_listV (s.(graph_in_state)))).
      {
        eapply NoDup_length_incl.
        * apply bijective_listV_NoDup; auto.
        * rewrite Hlen; lia.
        * exact Hincl.
      }
      split.
      * intros x; split; intros Hx.
        {
          apply Hismst.
          apply Hsub; auto.
        }
        {
          apply bijective_vertices; [apply Hgvalid|].
          apply Hincl_rev.
          apply bijective_vertices; auto.
        }
      * intros; apply Hismst.
        apply Hsub; auto.
    }
    split; [split; [|split]|]; auto.
    intros q Hq.
    destruct Hismst as [Hismst Hmin].
    pose proof Hq as Hq'.
    apply Hmin in Hq.
    set (sumE := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
    assert (Hperm_sum : forall l1 l2, Permutation l1 l2 -> sumE l1 = sumE l2).
    {
      intros l1 l2 Hperm.
      induction Hperm; subst sumE; simpl; auto.
      - rewrite IHHperm; auto.
      - rewrite !Z_op_plus_assoc.
        rewrite (Z_op_plus_comm (weight g x) (weight g y0)).
        reflexivity.
      - rewrite IHHperm1, IHHperm2; auto.
    }
    eapply Z_op_le_trans; eauto.
    assert (HpermE:
      Permutation (bijective_listE (s.(graph_in_state))) (bijective_listE y)).
    {
      apply NoDup_Permutation; try apply bijective_listE_NoDup;
      [apply Hgvalid | apply Hismst | ]; auto.
      intros e; rewrite ! bijective_edges;
      [| apply Hismst| apply Hgvalid]; auto.
      split; intros He.
      - apply no_empty_edge in He as [u [v Hstep]]; [|apply Hgvalid].
        apply Hsub in Hstep.
        eapply step_evalid; eauto.
      - apply no_empty_edge in He as [u [v Hstep]]; [|apply Hismst].
        assert (Hu: vvalid s.(graph_in_state) u) by (apply Hsubeq; apply Hismst; eapply step_vvalid1; eauto).
        assert (Hv: vvalid s.(graph_in_state) v) by (apply Hsubeq; apply Hismst; eapply step_vvalid2; eauto).
        apply NNPP; intros He.
        pose proof Htree as Htree_conn.
        apply tree_connected in Htree_conn.
        pose proof (Htree_conn u v Hu Hv) as Hreach.
        apply reachable_valid_epath in Hreach as [p Hp].
        assert (~ In e p). {
          intros Hin; apply He; apply in_split in Hin as [l1 [l2 Hin]]; subst.
          eapply valid_epath_app_inv in Hp as [w [Hpre Hrest]]; auto.
          apply valid_epath_cons_inv in Hrest as [x [Hstep' _]].
          eapply step_evalid; eauto.
        }
        eapply valid_epath_simple_Forall with (eset := fun a => ~ a = e) in Hp as [r [[Hrvalid Hrnodup] Hrfor]].
        2:{ intros; eapply step_aux_unique_undirected with (g:= (s.(graph_in_state))); eauto. }
        2:{ rewrite Forall_forall in *.
          intros x Hx ?; subst; auto. }
        destruct Hismst as [_ [Htree_y _]].
        apply tree_no_curcuit in Htree_y.
        apply Htree_y.
        exists u, (r ++ e :: nil); split;
        [symmetry; apply app_cons_not_nil|].
        assert (Hpath: forall x l z, valid_epath (s.(graph_in_state)) x l z -> valid_epath y x l z). {
            intros x l.
            revert x.
            induction l as [|a l IHl]; intros x z Hpath.
            - apply valid_epath_nil_inv in Hpath; subst.
              apply valid_epath_empty.
            - apply valid_epath_cons_inv in Hpath as [w [Hstep_path Hrest]].
              eapply valid_epath_cons.
              + apply Hsub; exact Hstep_path.
              + apply IHl; exact Hrest.
        } apply Hpath in Hrvalid.
        split.
        + eapply valid_epath_snoc; eauto.
          apply step_sym; auto.
        + apply Nodup_app_comm.
          simpl; constructor; auto.
          rewrite Forall_forall in *; intros He';
          apply Hrfor in He'; auto.
    }
    unfold sumE in Hperm_sum.
    apply Hperm_sum in HpermE.
    unfold total_weight.
    rewrite HpermE.
    destruct ((fold_right Z_op_plus (Some 0) (map (weight g) (bijective_listE y)))); simpl; [lia|auto].
  }
Qed.


End Prim.
