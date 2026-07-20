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
        {add_edge_exist: addEdgeExist G V E}
        {addEdgeGValid: addEdgeGValid G V E}
        {emptyGraph: emptyGraph G V E src}.

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
    assert ((exists y : G, is_mst g y /\ subgraph2 (graph_in_state s) y)) by (eapply prim_step; eauto).
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
    + eapply connected_have_mst in g_connected as [y Hy]; eauto. 
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


End Prim.
