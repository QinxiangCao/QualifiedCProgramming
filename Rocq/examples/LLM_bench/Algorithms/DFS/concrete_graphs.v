Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
From SumLib Require Import ZRange.

Local Open Scope Z_scope.

(** Dense integer-indexed simple directed graphs.  An edge is identified by
    its ordered pair of endpoints, so parallel edges are impossible. *)
Module ZSimpleGraph.

Definition V : Type := Z.
Definition E : Type := (Z * Z)%type.

Record G : Type := mkG {
  vertex_count : Z;
  adjacency : V -> V -> Prop;
}.

Definition vertex_valid (g : G) (v : V) : Prop :=
  0 <= v < vertex_count g.

Definition graph_step (g : G) (u v : V) : Prop :=
  vertex_valid g u /\
  vertex_valid g v /\
  adjacency g u v.
 
Definition edge_valid (g : G) (e : E) : Prop :=
  graph_step g (fst e) (snd e).

Definition graph_wf (g : G) : Prop :=
  0 <= vertex_count g /\
  forall v, vertex_valid g v -> ~ adjacency g v v.

Definition vertices (g : G) : list V :=
  Zrange 0 (vertex_count g).

(** Shared pure relation used by concrete DFS implementations whose visited
    set is stored as a dense 0/1 integer array. *)
Definition visited_values
    (g : G) (values : list Z) (visited_set : V -> Prop) : Prop :=
  Zlength values = vertex_count g /\
  (forall v, visited_set v -> vertex_valid g v) /\
  forall v,
    vertex_valid g v ->
    (Znth v values 0 = 0 \/ Znth v values 0 = 1) /\
    (visited_set v <-> Znth v values 0 = 1).

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := vertex_valid;
  evalid := edge_valid;
  step_aux := fun g e u v => e = (u, v) /\ graph_step g u v;
|}.

#[export] Instance gvalid_instance : GValid G := graph_wf.

#[export] Instance stepvalid_instance : StepValid G V E.
Proof.
  constructor.
  - intros g e u v [_ [Hu _]]. exact Hu.
  - intros g e u v [_ [_ [Hv _]]]. exact Hv.
  - intros g e u v [-> Hstep].
    unfold edge_valid; simpl; exact Hstep.
Qed.

#[export] Instance noempty_instance : NoEmptyEdge G V E.
Proof.
  constructor.
  intros g [u v] Hg He.
  exists u, v. split; [reflexivity | exact He].
Qed.

#[export] Instance stepunique_instance : StepUniqueDirected G V E.
Proof.
  constructor.
  intros g e x1 y1 x2 y2 Hg [He1 _] [He2 _].
  rewrite He1 in He2; inversion He2; auto.
Qed.

#[export] Instance simple_instance : SimpleGraph G V E.
Proof.
  constructor.
  - intros g e1 e2 x y Hg [He1 _] [He2 _].
    rewrite He1, He2. reflexivity.
  - intros g e x Hg [_ [Hx [_ Hloop]]].
    destruct Hg as [_ Hirrefl].
    exact (Hirrefl x Hx Hloop).
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := vertices |}.
  intros g Hg v Hv.
  unfold vertices, vertex_valid in *.
  apply In_Zrange. exact Hv.
Defined.

#[export] Instance vlist_bijective_instance : VListBijective G V E.
Proof.
  refine {| bijective_listV := vertices |}.
  - intros g Hg. unfold vertices. apply NoDup_Zrange.
  - intros g Hg v.
    unfold vertices, vertex_valid.
    rewrite <- In_Zrange. reflexivity.
Defined.

Lemma step_iff : forall g u v,
  step g u v <-> graph_step g u v.
Proof.
  intros g u v. unfold step; split.
  - intros [[x y] [He Hstep]].
    inversion He; exact Hstep.
  - intros Hstep. exists (u, v). split; [reflexivity | exact Hstep].
Qed.

End ZSimpleGraph.


(** Dense integer-indexed directed multigraphs.  Edge identifiers are part of
    the mathematical graph, so distinct identifiers may have equal endpoints. *)
Module ZMultigraph.

Definition V : Type := Z.
Definition E : Type := Z.

Record G : Type := mkG {
  vertex_count : Z;
  edge_count : Z;
  edge_src : E -> V;
  edge_dst : E -> V;
}.

Definition vertex_valid (g : G) (v : V) : Prop :=
  0 <= v < vertex_count g.

Definition edge_index_valid (g : G) (e : E) : Prop :=
  0 <= e < edge_count g.

Definition edge_valid (g : G) (e : E) : Prop :=
  edge_index_valid g e /\
  vertex_valid g (edge_src g e) /\
  vertex_valid g (edge_dst g e).

Definition graph_step (g : G) (e : E) (u v : V) : Prop :=
  edge_valid g e /\
  u = edge_src g e /\
  v = edge_dst g e.

Definition graph_wf (g : G) : Prop :=
  0 <= vertex_count g /\
  0 <= edge_count g /\
  forall e, edge_index_valid g e ->
    vertex_valid g (edge_src g e) /\
    vertex_valid g (edge_dst g e).

Definition vertices (g : G) : list V :=
  Zrange 0 (vertex_count g).

Definition edges (g : G) : list E :=
  Zrange 0 (edge_count g).

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := vertex_valid;
  evalid := edge_valid;
  step_aux := graph_step;
|}.

#[export] Instance gvalid_instance : GValid G := graph_wf.

#[export] Instance stepvalid_instance : StepValid G V E.
Proof.
  constructor.
  - intros g e u v [He [-> _]].
    unfold edge_valid in He. tauto.
  - intros g e u v [He [_ ->]].
    unfold edge_valid in He. tauto.
  - intros g e u v [He _]. exact He.
Qed.

#[export] Instance noempty_instance : NoEmptyEdge G V E.
Proof.
  constructor.
  intros g e Hg He.
  change (edge_valid g e) in He.
  exists (edge_src g e), (edge_dst g e).
  unfold graph_step.
  split; [exact He | split; reflexivity].
Qed.

#[export] Instance stepunique_instance : StepUniqueDirected G V E.
Proof.
  constructor.
  intros g e x1 y1 x2 y2 Hg [_ [Hx1 Hy1]] [_ [Hx2 Hy2]].
  subst; auto.
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := vertices |}.
  intros g Hg v Hv.
  unfold vertices, vertex_valid in *.
  apply In_Zrange. exact Hv.
Defined.

#[export] Instance vlist_bijective_instance : VListBijective G V E.
Proof.
  refine {| bijective_listV := vertices |}.
  - intros g Hg. unfold vertices. apply NoDup_Zrange.
  - intros g Hg v.
    unfold vertices, vertex_valid.
    rewrite <- In_Zrange. reflexivity.
Defined.

#[export] Instance finite_edges_instance : FiniteEGraph G V E.
Proof.
  refine {| listE := edges |}.
  intros g Hg e He.
  change (edge_valid g e) in He.
  unfold edges.
  apply In_Zrange.
  exact (proj1 He).
Defined.

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := edges |}.
  - intros g Hg. unfold edges. apply NoDup_Zrange.
  - intros g Hg e.
    destruct Hg as [_ [_ Hendpoints]].
    unfold edges, edge_valid, edge_index_valid.
    rewrite <- In_Zrange.
    split.
    + intros He. split; [exact He | exact (Hendpoints e He)].
    + change (edge_valid g e -> edge_index_valid g e).
      intros He. exact (proj1 He).
Defined.

Lemma step_iff : forall g u v,
  step g u v <-> exists e, graph_step g e u v.
Proof.
  intros. reflexivity.
Qed.

End ZMultigraph.
