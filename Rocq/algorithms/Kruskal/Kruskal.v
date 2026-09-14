Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted subgraph path path_basic vpath epath Zweight.
From GraphLib Require Import tree kruskal prim.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import NoDup.
Require Import Algorithms.MapLib.
Require Import Algorithms.Prim.Prim.

Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.

Section Kruskal.

Class initialForest (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  initial_forest: G -> G;
  initial_forest_valid:
    forall g, gvalid g -> gvalid (initial_forest g);
  initial_forest_vvalid:
    forall g v, vvalid (initial_forest g) v <-> vvalid g v;
  initial_forest_evalid:
    forall g e, evalid (initial_forest g) e <-> False;
}. 

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noempty: NoEmptyEdge G V E}
        {undirected: UndirectedGraph G V E}
        {stepuniq: StepUniqueUndirected G V E}
        {finitegraph: FiniteGraph G V E}
        {elistbijective: EListBijective G V E}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Context {g: G}
        {g_valid: gvalid g}
        {g_connected: connected g}
        {add_edge_in_subgraph: addEdgeInSubgraph G V E}
        {addEdgeGValid: addEdgeGValid G V E}.

Record St: Type := mkSt {
  graph_in_state: G;
}.

Context {tr: Tree G V E P}
        {initial_forest_graph: initialForest G V E}.

(** 初始状态：保留原图全部顶点，边集为空。 *)
Definition initSt: St := {| graph_in_state := initial_forest g |}.

Instance: Settable St := settable! mkSt <graph_in_state>.

(** 将边e加入生成树边集 *)
Definition add_to_mst (u v: V) (e: E): program St unit :=
  update (fun s1 s2: St => addEdge (s1.(graph_in_state)) (s2.(graph_in_state)) u v e). 

Definition selectable_edge (s: St) (e: E): Prop := 
  evalid g e /\
  forall u v, step_aux g e u v ->
    ~ reachable (graph_in_state s) u v.

(** 从所有有效且不形成环的边中选择权重最小的 *)
Definition get_min_edge (f: St -> E -> Prop): program St E :=
  get (fun s e => min_object_of_subset Z_op_le (f s) (weight g) e).

(** Kruskal主算法：循环直到没有可选边 *)
Definition Kruskal: program St unit :=
  whileP (fun s => exists e, selectable_edge s e)
    (
      e <- get_min_edge selectable_edge;;  (* 选择最小权重的可选边 *)
      x <- get (fun s '(u, v) => step_aux g e u v);;
      add_to_mst (fst x) (snd x) e                    (* 将边加入边集 *)
    ).

(* Kruskal算法的正确性 *)
Theorem Kruskal_correct:
  Hoare (fun s => s = initSt)
        Kruskal
        (fun _ s => is_mst g (graph_in_state s)).
Proof. 
  eapply Hoare_conseq. 
  3:{
    unfold Kruskal. 
    eapply Hoare_whileP with (P := fun s => 
    ((forall u, ~ exists p, is_simple_epath (graph_in_state s) u p u /\ p <> nil) /\ 
    (exists y1, is_mst g y1 /\ subgraph2 (graph_in_state s) y1)) /\ 
    (gvalid (graph_in_state s)) /\
    subgraph_vertex_eq (graph_in_state s) g).
    intro_state. 
    unfold get_min_edge, add_to_mst.
    hoare_auto_s. 
    destruct H as [_ [[Hno_circuit [y1 [Hmst1 Hsubgraph1]]]
      [Hgvalid Hvertexeq]]].
    destruct a0 as (u, v). 
    rename a into e; simpl in *. 
    split.
    - eapply kruskal_step; eauto.
    - split.
      + eapply addEdge_gvalid; eauto.
      + pose proof Hvertexeq as [Hvertices Hsteps].
        assert (Hu0 : vvalid (graph_in_state s0) u).
        {
          apply Hvertices.
          eapply step_vvalid1; eauto.
        }
        assert (Hv0 : vvalid (graph_in_state s0) v).
        {
          apply Hvertices.
          eapply step_vvalid2; eauto.
        }
        split.
        * intros z.
          rewrite (addEdge2_vvalid_iff
            (graph_in_state s0) (graph_in_state s) u v e Hu0 Hv0 H2).
          apply Hvertices.
        * intros z w a Hstep.
          destruct H2 as [_ _ Haddstep].
          apply Haddstep in Hstep as [Hold | [-> [[-> ->] | [-> ->]]]].
          -- apply Hsteps; exact Hold.
          -- exact H1.
          -- apply step_sym; exact H1.
  } 
  {
    intros; subst; split; [split|split].
    + simpl; intros u [p []]. 
      destruct p; [contradiction|]. 
      destruct H as [H _]. 
      apply valid_epath_cons_inv in H as [v []]. 
      eapply step_evalid in H. 
      rewrite initial_forest_evalid in H.
      auto. 
    + destruct (Algorithms.Prim.Prim.connected_have_mst_in_subgraph
        g g_connected g_valid) as [y Hy].
      exists y. split; auto.
      pose proof (is_mst_legal g y Hy) as [_ [_ Hsubeq]].
      destruct Hsubeq as [Hsubv Hsubs].
      split. 
      {
        intros x Hx.
        apply Hsubv.
        exact (proj1 (initial_forest_vvalid g x) Hx).
      }
      { 
        intros u v e Hstep. 
        exfalso; eapply step_evalid in Hstep. 
        exact (proj1 (initial_forest_evalid g e) Hstep).
      } 
    + exact (initial_forest_valid g g_valid).
    + split.
      * intros x. apply initial_forest_vvalid.
      * intros u v e Hstep.
        exfalso.
        apply step_evalid in Hstep.
        exact (proj1 (initial_forest_evalid g e) Hstep).
  } 
  { 
    simpl; intros _ s [Hinv Hexit].
    destruct Hinv as [[Hno_circuit [y [Hmst Hsub]]]
      [Hgvalid Hvertexeq]].
    pose proof (is_mst_legal g y Hmst)
      as [Hyvalid [Htree_y Hsubeq_y]].
    assert (Hedge_sub:
      forall e, evalid y e -> evalid (graph_in_state s) e).
    {
      intros e He_y.
      apply NNPP; intros He_not.
      apply Hexit.
      exists e.
      split.
      - pose proof (no_empty_edge y e Hyvalid He_y) as [a [b Hstep_y]].
        eapply step_evalid.
        apply Hsubeq_y; exact Hstep_y.
      - intros u v Hstep_g Hreach.
        apply He_not.
        assert (Hstep_y_uv : step_aux y e u v).
        {
          pose proof (no_empty_edge y e Hyvalid He_y) as [a [b Hstep_y]].
          assert (Hstep_y_g : step_aux g e a b) by (apply Hsubeq_y; auto).
          eapply step_aux_unique_undirected in Hstep_g as [[]|[]]; eauto; subst;
          [|apply step_sym]; auto.
        }
        destruct (reachable_valid_epath (graph_in_state s) u v Hreach) as [p Hp].
        assert (Hnotin : ~ In e p).
        {
          intros Hin.
          apply He_not.
          eapply in_epath_evalid; eauto.
        }
        eapply valid_epath_simple_Forall with (eset := fun a => ~ a = e) in Hp
          as [q [[Hqvalid Hqnodup] Hqfor]].
        2:{ intros; eapply step_aux_unique_undirected with (g:= graph_in_state s); eauto. }
        2:{ rewrite Forall_forall. intros a Ha Heq; subst; apply Hnotin; auto. }
        assert (Hpath_y : valid_epath y u q v).
        {
          assert (Hpath_sub: forall x0 l z0,
            valid_epath (graph_in_state s) x0 l z0 ->
            valid_epath y x0 l z0).
          {
            intros x0 l.
            revert x0.
            induction l as [|a l IH]; intros x0 z0 Hpath.
            - apply valid_epath_nil_inv in Hpath; subst.
              apply valid_epath_empty.
            - apply valid_epath_cons_inv in Hpath as [w [Hstep Hrest]].
              eapply valid_epath_cons.
              + apply Hsub; eauto.
              + apply IH; auto.
          }
          apply Hpath_sub; auto.
        }
        apply tree_no_curcuit in Htree_y.
        exfalso; apply Htree_y.
        exists u, (q ++ e :: nil).
        split; [symmetry; apply app_cons_not_nil|].
        split.
        + eapply valid_epath_snoc; eauto.
          apply step_sym; exact Hstep_y_uv.
        + apply Nodup_app_comm.
          simpl; constructor; auto.
          rewrite Forall_forall in Hqfor.
          intros Hin; apply Hqfor in Hin; auto.
    }
    assert (Htree_s : tree (graph_in_state s)).
    {
      apply tree_decide.
      - intros x y0 Hx Hy0.
      pose proof (tree_connected y Htree_y x y0 ltac:(apply Hsub; auto) ltac:(apply Hsub; auto)) as Hreach_y.
      destruct (reachable_valid_epath y x y0 Hreach_y) as [p Hp].
      eapply valid_epath_reachable.
      assert (Hpath_cur : valid_epath (graph_in_state s) x p y0).
      {
        assert (Hpath_sub: forall x0 l z0,
          valid_epath y x0 l z0 ->
          valid_epath (graph_in_state s) x0 l z0).
        {
          intros x0 l.
          revert x0.
          induction l as [|e l IH]; intros x0 z0 Hpath.
          - apply valid_epath_nil_inv in Hpath; subst.
            apply valid_epath_empty.
          - apply valid_epath_cons_inv in Hpath as [w [Hstep_y Hrest]].
            assert (He_cur : evalid (graph_in_state s) e) by (apply Hedge_sub; eapply step_evalid; eauto).
            pose proof (no_empty_edge (graph_in_state s) e Hgvalid He_cur) as [a [b Hstep_cur]].
            assert (Hstep_cur_y : step_aux y e a b) by (apply Hsub; auto).
            eapply step_aux_unique_undirected in Hstep_y as [[Hxz Hzb] | [Hxb Hza]]; eauto; subst.
            + eapply valid_epath_cons; eauto.
            + eapply valid_epath_cons; [apply step_sym; exact Hstep_cur|].
              apply IH; auto.
        }
        apply Hpath_sub; auto.
      }
      exact Hpath_cur.
    - intros [x [p [Hpne Hsimple]]].
      eapply (Hno_circuit x).
      exists p; split; auto.
    }
    assert (Hcurrent_sub_y:
      forall e, evalid (graph_in_state s) e -> evalid y e).
    {
      intros e He.
      destruct (no_empty_edge (graph_in_state s) e Hgvalid He)
        as [u [v Hstep]].
      eapply step_evalid.
      apply Hsub; exact Hstep.
    }
    assert (Hedge_perm:
      Permutation
        (bijective_listE (graph_in_state s))
        (bijective_listE y)).
    {
      apply NoDup_Permutation.
      - apply bijective_listE_NoDup; exact Hgvalid.
      - apply bijective_listE_NoDup; exact Hyvalid.
      - intros e.
        rewrite (bijective_edges (graph_in_state s) Hgvalid).
        rewrite (bijective_edges y Hyvalid).
        split; auto.
    }
    assert (Hweight:
      total_weight g (graph_in_state s) = total_weight g y).
    {
      unfold total_weight.
      set (sumE := fun l =>
        fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
      assert (Hperm_sum:
        forall l1 l2, Permutation l1 l2 -> sumE l1 = sumE l2).
      {
        intros l1 l2 Hperm.
        induction Hperm; subst sumE; simpl; auto.
        - rewrite IHHperm; auto.
        - rewrite !Z_op_plus_assoc.
          rewrite (Z_op_plus_comm (weight g x) (weight g y0)).
          reflexivity.
        - rewrite IHHperm1, IHHperm2; auto.
      }
      apply Hperm_sum; exact Hedge_perm.
    }
    unfold is_mst, min_object_of_subset.
    split.
    - split; [exact Hgvalid|].
      split; [exact Htree_s|exact Hvertexeq].
    - intros h Hlegal.
      destruct Hmst as [_ Hminimal].
      rewrite Hweight.
      apply Hminimal; exact Hlegal.
  }
Qed.

End Kruskal.
