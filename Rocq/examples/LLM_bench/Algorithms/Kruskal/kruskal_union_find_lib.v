Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
Require Import ListLib.Base.Positional.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
From MonadLib.StateRelMonad Require Export StateRelBasic.
From MonadLib.StateRelMonad Require Import StateRelHoare FixpointLib safeexec_lib.
From MonadLib.Examples Require Export union_find_err.
Require Algorithms.Kruskal.Kruskal.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Import naive_C_Rules.
Local Open Scope sac.

(** * Kruskal 边表版本的具体图模型 *)

Definition V : Type := Z.
Definition E : Type := Z.

Record G : Type := mkG {
  graph_from : E -> V;
  graph_to : E -> V;
  graph_weight : E -> Z;
  graph_vertices : list V;
  graph_edges : list E;
}.

Definition edge_src (g : G) (e : E) : V :=
  graph_from g e.

Definition edge_dst (g : G) (e : E) : V :=
  graph_to g e.

Definition graph_edge_count (g : G) : Z :=
  Zlength (graph_edges g).

Definition graph_vertex_count (g : G) : Z :=
  Zlength (graph_vertices g).

Definition edge_endpoints_valid (g : G) (e : E) : Prop :=
  In (edge_src g e) (graph_vertices g) /\
  In (edge_dst g e) (graph_vertices g).

Definition graph_step (g : G) (e : E) (u v : V) : Prop :=
  In e (graph_edges g) /\
  edge_endpoints_valid g e /\
  ((u = edge_src g e /\ v = edge_dst g e) \/
   (u = edge_dst g e /\ v = edge_src g e)).

Definition graph_wf (g : G) : Prop :=
  forall e, In e (graph_edges g) -> exists u v, graph_step g e u v.

(** ** GraphLib 接口实例 *)

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := fun g v => In v (graph_vertices g);
  evalid := fun g e => In e (graph_edges g);
  step_aux := graph_step;
|}.

#[export] Instance gvalid_instance : GValid G := graph_wf.

#[export] Instance stepvalid_instance : StepValid G V E.
Proof.
  constructor.
  - intros g e x y Hstep.
    destruct Hstep as [_ [[Hsrc Hdst] Hends]].
    destruct Hends as [[-> ->] | [-> ->]]; auto.
  - intros g e x y Hstep.
    destruct Hstep as [_ [[Hsrc Hdst] Hends]].
    destruct Hends as [[-> ->] | [-> ->]]; auto.
  - intros g e x y Hstep.
    destruct Hstep as [He _]; exact He.
Qed.

#[export] Instance noempty_instance : NoEmptyEdge G V E.
Proof.
  constructor.
  intros g e Hg He.
  exact (Hg e He).
Qed.

#[export] Instance undirected_instance : UndirectedGraph G V E.
Proof.
  constructor.
  intros g e x y Hstep.
  destruct Hstep as [He [Hends [[Hx Hy] | [Hx Hy]]]]; subst.
  - split; [exact He | split; [exact Hends | right; auto]].
  - split; [exact He | split; [exact Hends | left; auto]].
Qed.

#[export] Instance stepunique_instance : StepUniqueUndirected G V E.
Proof.
  constructor.
  intros g e x1 y1 x2 y2 _ H1 H2.
  destruct H1 as [_ [_ Hxy1]].
  destruct H2 as [_ [_ Hxy2]].
  destruct Hxy1 as [[-> ->] | [-> ->]];
    destruct Hxy2 as [[-> ->] | [-> ->]]; auto.
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := graph_vertices |}.
  intros g _ v Hv; exact Hv.
Qed.

#[export] Instance finiteE_instance : FiniteEGraph G V E.
Proof.
  refine {| listE := graph_edges |}.
  intros g _ e He; exact He.
Qed.

Definition valid_edges (g : G) : list E :=
  nodup Z.eq_dec (graph_edges g).

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := valid_edges |}.
  - intros g _.
    unfold valid_edges.
    apply NoDup_nodup.
  - intros g _ e.
    unfold valid_edges.
    rewrite nodup_In.
    tauto.
Qed.

#[export] Instance edge_weight_instance : EdgeWeight G E := {|
  weight := fun g e => Some (graph_weight g e);
|}.


(** * 具体路径模型 *)

Record path: Type := mkpath {
  path_edges: list (E*V);
  path_start: V;
}.

Definition path_vertices (p : path) : list V :=
  path_start p :: map snd (path_edges p).

Definition path_edge_ids (p : path) : list E :=
  map fst (path_edges p).

Definition path_head (p : path) : V :=
  path_start p.

Definition path_tail (p : path) : V :=
  last (path_vertices p) 0.

Definition empty_path_impl (v : V) : path :=
  mkpath nil v.

Definition single_path_impl (u v : V) (e : E) : path :=
  mkpath ((e, v) :: nil) u.

Definition concat_path_impl (p q : path) : path :=
  mkpath (path_edges p ++ path_edges q) (path_start p).

Definition P : Type := path.

Definition path_valid_prop (g : G) (p : path) : Prop :=
  vpath_iff_epath_prop g (path_vertices p) (path_edge_ids p).

(** * 路径辅助引理 *)

Lemma path_vertices_nonempty :
  forall p, path_vertices p <> nil.
Proof.
  intros p.
  unfold path_vertices.
  destruct p; simpl; discriminate.
Qed.

Lemma path_tail_valid :
  forall p, Some (path_tail p) = tl_error (path_vertices p).
Proof.
  intros p.
  unfold path_tail.
  pose proof (path_vertices_nonempty p) as Hnonempty.
  apply exists_last in Hnonempty as [prefix [x Hx]].
  rewrite Hx.
  rewrite tl_error_last.
  rewrite last_last.
  reflexivity.
Qed.

Lemma nth_error_path_vertices_last :
  forall (s : V) (es : list (E * V)),
    nth_error (s :: map snd es) (length es) =
    Some (last (s :: map snd es) 0).
Proof.
  intros s es.
  revert s.
  induction es as [| [e v] es IH]; intros s; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma nth_error_concat_vertices_boundary_app :
  forall (s1 : V) (es1 : list (E * V)) (s2 : V) (es2 : list (E * V)),
    last (s1 :: map snd es1) 0 = s2 ->
    nth_error ((s1 :: map snd es1) ++ map snd es2) (length es1) =
    nth_error (s2 :: map snd es2) 0.
Proof.
  intros s1 es1 s2 es2 Htail.
  rewrite nth_error_app1 by (simpl; rewrite length_map; lia).
  rewrite nth_error_path_vertices_last.
  rewrite Htail.
  reflexivity.
Qed.

Lemma nth_error_concat_vertices_after_app :
  forall (s1 : V) (es1 : list (E * V)) (s2 : V) (es2 : list (E * V)) k,
    nth_error ((s1 :: map snd es1) ++ map snd es2) (length es1 + S k) =
    nth_error (s2 :: map snd es2) (S k).
Proof.
  intros s1 es1 s2 es2 k.
  rewrite nth_error_app2 by (simpl; rewrite length_map; lia).
  replace (length es1 + S k - length (s1 :: map snd es1))%nat with k
    by (simpl; rewrite length_map; lia).
  reflexivity.
Qed.

(** * GraphLib 路径接口实例 *)

#[export] Instance path_instance : Path G V E P.
Proof.
  refine {|
    path_valid := path_valid_prop;
    vertex_in_path := path_vertices;
    head := path_head;
    head_valid := _;
    tail := path_tail;
    tail_valid := _;
    edge_in_path := path_edge_ids;
    vpath_iff_epath := _;
  |}.
  - intros g p Hvalid.
    unfold path_head, path_vertices.
    destruct p; reflexivity.
  - intros g p Hvalid.
    apply path_tail_valid.
  - intros g p Hvalid.
    exact Hvalid.
Defined.

#[export] Instance emptypath_instance :
  EmptyPath G V E P path_instance.
Proof.
  refine {|
    empty_path := empty_path_impl
  |}.
  - intros g v.
    split.
    + reflexivity.
    + intros n u w e Hn _ _ _.
      simpl in Hn; lia.
  - intros v; reflexivity.
Defined.

Lemma single_path_valid_impl :
  forall g u v e,
    step_aux g e u v ->
    path_valid g (single_path_impl u v e).
Proof.
  intros g u v e Hstep.
  unfold path_valid, path_instance, path_valid_prop,
    single_path_impl, path_vertices, path_edge_ids.
  simpl.
  split.
  - reflexivity.
  - intros n u' v' e' Hn He Hu Hv.
    destruct n as [| n]; [| simpl in Hn; lia].
    simpl in He, Hu, Hv.
    inversion He; inversion Hu; inversion Hv; subst.
    exact Hstep.
Qed.

#[export] Instance singlepath_instance :
  SinglePath G V E P path_instance.
Proof.
  refine {|
    single_path := single_path_impl;
    single_path_valid := single_path_valid_impl;
    single_path_vertex := _;
    single_path_edge := _;
  |}.
  - intros u v e; reflexivity.
  - intros u v e; reflexivity.
Defined.

Lemma concat_path_valid_impl :
  forall g a1 a2,
    path_valid g a1 ->
    path_valid g a2 ->
    tail a1 = head a2 ->
    path_valid g (concat_path_impl a1 a2).
Proof.
  intros g [es1 s1] [es2 s2] Hvalid1 Hvalid2 Hjoin.
  unfold path_valid, path_instance, path_valid_prop,
    concat_path_impl, path_vertices, path_edge_ids, path_tail, path_head
    in Hvalid1, Hvalid2, Hjoin |- *.
  simpl in Hvalid1, Hvalid2, Hjoin |- *.
  destruct Hvalid1 as [_ Hstep1].
  destruct Hvalid2 as [_ Hstep2].
  split.
  - simpl.
    repeat rewrite length_map.
    lia.
  - intros n u v e Hn He Hu Hv.
    rewrite map_app in He.
    rewrite map_app in Hu, Hv.
    change (s1 :: map snd es1 ++ map snd es2)
      with ((s1 :: map snd es1) ++ map snd es2) in Hu.
    change (s1 :: map snd es1 ++ map snd es2)
      with ((s1 :: map snd es1) ++ map snd es2) in Hv.
    destruct (lt_dec n (length es1)) as [Hleft | Hright].
    + eapply Hstep1.
      * split; [lia | rewrite length_map; exact Hleft].
      * rewrite nth_error_app1 in He by (rewrite length_map; exact Hleft).
        exact He.
      * rewrite nth_error_app1 in Hu by (simpl; rewrite length_map; lia).
        exact Hu.
      * rewrite nth_error_app1 in Hv by (simpl; rewrite length_map; lia).
        exact Hv.
    + pose (k := (n - length es1)%nat).
      assert (Hn_eq : n = (length es1 + k)%nat) by (unfold k; lia).
      replace n with (length es1 + k)%nat in * by (symmetry; exact Hn_eq).
      rewrite nth_error_app2 in He by (rewrite length_map; lia).
      replace (length es1 + k - length (map fst es1))%nat with k in He
        by (rewrite length_map; lia).
      destruct k as [| k].
      * eapply Hstep2.
        -- split; [lia | apply nth_error_Some; rewrite He; discriminate].
        -- exact He.
        -- replace (length es1 + 0)%nat with (length es1) in Hu by lia.
           rewrite (nth_error_concat_vertices_boundary_app s1 es1 s2 es2 Hjoin) in Hu.
           exact Hu.
        -- replace (S (length es1 + 0))%nat with (length es1 + S 0)%nat in Hv by lia.
           rewrite (nth_error_concat_vertices_after_app s1 es1 s2 es2 0) in Hv.
           exact Hv.
      * eapply Hstep2.
        -- split; [lia | apply nth_error_Some; rewrite He; discriminate].
        -- exact He.
        -- rewrite (nth_error_concat_vertices_after_app s1 es1 s2 es2 k) in Hu.
           exact Hu.
        -- replace (S (length es1 + S k))%nat with (length es1 + S (S k))%nat in Hv by lia.
           rewrite (nth_error_concat_vertices_after_app s1 es1 s2 es2 (S k)) in Hv.
           exact Hv.
Qed.

#[export] Instance concatpath_instance :
  ConcatPath G V E P path_instance.
Proof.
  refine {|
    concat_path := concat_path_impl;
    concat_path_valid := concat_path_valid_impl;
    concat_path_vertex := _;
    concat_path_edge := _;
  |}.
  - intros a1 a2.
    unfold concat_path_impl, path_vertices.
    destruct a1 as [es1 s1], a2 as [es2 s2].
    change (s1 :: map snd (es1 ++ es2) =
      (s1 :: map snd es1) ++ map snd es2).
    rewrite map_app.
    reflexivity.
  - intros a1 a2.
    unfold concat_path_impl, path_edge_ids.
    destruct a1 as [es1 s1], a2 as [es2 s2].
    change (map fst (es1 ++ es2) = map fst es1 ++ map fst es2).
    rewrite map_app.
    reflexivity.
Defined.

#[export] Instance destruct1npath_instance :
  Destruct1nPath G V E P path_instance
    emptypath_instance singlepath_instance concatpath_instance.
Proof.
  unshelve econstructor.
  - intros g [es s] Hvalid.
    destruct es as [| [e v] es].
    + exact (DestructBase1n s).
    + exact (DestructStep1n (mkpath es v) s v e).
  - intros g [es s] Hvalid.
    unfold path_cons_spec.
    destruct es as [| [e v] es].
    + reflexivity.
    + simpl.
      unfold path_valid, path_instance, path_valid_prop,
        path_vertices, path_edge_ids, path_head in Hvalid |- *.
      simpl in Hvalid |- *.
      destruct Hvalid as [Hlen Hstep].
      split.
      * split.
        -- simpl in Hlen.
           simpl.
           repeat rewrite length_map in Hlen |- *.
           lia.
        -- intros i x y a Hi Ha Hu Hy.
           eapply Hstep with (n := S i).
           ++ simpl.
              repeat rewrite length_map in Hi |- *.
              lia.
           ++ simpl.
              exact Ha.
           ++ simpl.
              exact Hu.
           ++ simpl.
              exact Hy.
      * split.
        -- reflexivity.
        -- split.
           ++ eapply Hstep with (n := 0%nat).
              ** simpl.
                 repeat rewrite length_map.
                 lia.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
           ++ reflexivity.
Defined.
#[export] Instance tree_instance :
  @Tree G V E graph_instance gvalid_instance P path_instance.
Proof.
  refine {|
    tree := fun g =>
      connected g /\
      ~ exists u p, p <> nil /\ is_simple_epath g u p u
  |}.
  - intros g [Hconnected _]; exact Hconnected.
  - intros g [_ Hacyclic]; exact Hacyclic.
  - intros g Hconnected Hacyclic; split; auto.
Defined.


(** * 输入三数组到抽象图的绑定 *)

Definition array_graph
    (n m : Z) (from to wt : list Z) (g : G) : Prop :=
  graph_vertices g = Zrange 0 n /\
  graph_edges g = Zrange 0 m /\
  0 <= n /\
  0 <= m /\
  Zlength from = m /\
  Zlength to = m /\
  Zlength wt = m /\
  (forall e, In e (Zrange 0 m) ->
    graph_from g e = Znth e from 0 /\
    graph_to g e = Znth e to 0 /\
    graph_weight g e = Znth e wt 0).

Definition uf_domain (n : Z) (x : Z) : Prop :=
  0 <= x < n.

Lemma Zlength_Zrange_aux :
  forall low n, Zlength (Zrange_aux low n) = Z.of_nat n.
Proof.
  intros low n.
  revert low.
  induction n as [| n IH]; intros low; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons, IH. lia.
Qed.

Lemma Zlength_Zrange :
  forall low high,
    low <= high ->
    Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle.
  unfold Zrange.
  rewrite Zlength_Zrange_aux.
  lia.
Qed.

Lemma array_graph_edge_count :
  forall n m from to wt g,
    array_graph n m from to wt g ->
    graph_edge_count g = m.
Proof.
  intros n m from to wt g Hgraph.
  unfold graph_edge_count.
  destruct Hgraph as [_ [Hedges [_ [Hm _]]]].
  rewrite Hedges.
  rewrite Zlength_Zrange by lia.
  lia.
Qed.

Lemma array_graph_vertex_count :
  forall n m from to wt g,
    array_graph n m from to wt g ->
    graph_vertex_count g = n.
Proof.
  intros n m from to wt g Hgraph.
  unfold graph_vertex_count.
  destruct Hgraph as [Hvertices [_ [Hn _]]].
  rewrite Hvertices.
  rewrite Zlength_Zrange by lia.
  lia.
Qed.

Lemma array_graph_vertex_in_uf_domain :
  forall n m from to wt g x,
    array_graph n m from to wt g ->
    In x (graph_vertices g) ->
    uf_domain n x.
Proof.
  intros n m from to wt g x Hgraph Hx.
  unfold uf_domain.
  destruct Hgraph as [Hvertices [_ [Hn _]]].
  rewrite Hvertices in Hx.
  rewrite <- In_Zrange in Hx.
  lia.
Qed.

Lemma array_graph_gvalid :
  forall n m from to wt g,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m ->
      0 <= Znth e from 0 < n /\
      0 <= Znth e to 0 < n) ->
    gvalid g.
Proof.
  intros n m from to wt g Hgraph Hendpoints.
  destruct Hgraph as
    [Hvertices [Hedges [Hn [Hm [Hfrom_len [Hto_len [Hwt_len Hentries]]]]]]].
  unfold gvalid, gvalid_instance, graph_wf.
  intros e He.
  assert (He_range : 0 <= e < m).
  {
    rewrite Hedges in He.
    rewrite <- In_Zrange in He.
    lia.
  }
  specialize (Hentries e).
  assert (He_zrange : In e (Zrange 0 m)).
  {
    rewrite <- In_Zrange.
    lia.
  }
  specialize (Hentries He_zrange).
  destruct Hentries as [Hfrom [Hto Hweight]].
  destruct (Hendpoints e He_range) as [Hfrom_range Hto_range].
  exists (graph_from g e), (graph_to g e).
  unfold graph_step, edge_endpoints_valid, edge_src, edge_dst.
  split; [exact He|].
  split.
  - rewrite Hvertices, Hfrom, Hto.
    split; rewrite <- In_Zrange; lia.
  - left; auto.
Qed.

Lemma array_graph_edge_endpoints_range :
  forall n m from to wt g e,
    array_graph n m from to wt g ->
    gvalid g ->
    0 <= e < m ->
    0 <= Znth e from 0 < n /\
    0 <= Znth e to 0 < n.
Proof.
  intros n m from to wt g e Hgraph Hg He_range.
  destruct Hgraph as
    [Hvertices [Hedges [Hn [Hm [Hfrom_len [Hto_len [Hwt_len Hentries]]]]]]].
  assert (He : In e (graph_edges g)).
  {
    rewrite Hedges, <- In_Zrange.
    lia.
  }
  destruct (Hg e He) as [u [v Hstep]].
  destruct Hstep as [_ [Hends _]].
  destruct Hends as [Hsrc Hdst].
  assert (He_zrange : In e (Zrange 0 m)).
  {
    rewrite <- In_Zrange.
    lia.
  }
  specialize (Hentries e He_zrange).
  destruct Hentries as [Hfrom [Hto Hweight]].
  unfold edge_src, edge_dst in Hsrc, Hdst.
  rewrite Hvertices in Hsrc, Hdst.
  rewrite <- In_Zrange in Hsrc, Hdst.
  rewrite <- Hfrom, <- Hto.
  lia.
Qed.

Definition add_edge_graph (g : G) (u v : V) (e : E) : G :=
  mkG
    (fun a => if Z.eq_dec a e then u else graph_from g a)
    (fun a => if Z.eq_dec a e then v else graph_to g a)
    (graph_weight g)
    (u :: v :: graph_vertices g)
    (e :: graph_edges g).

Definition remove_edge_graph (g : G) (e : E) : G :=
  mkG
    (graph_from g)
    (graph_to g)
    (graph_weight g)
    (graph_vertices g)
    (filter (fun a => if Z.eq_dec a e then false else true) (graph_edges g)).

Lemma add_edge_graph_vvalid :
  forall g u v e x,
    vvalid (add_edge_graph g u v e) x <-> vvalid g x \/ x = u \/ x = v.
Proof.
  intros g u v e x.
  unfold vvalid, graph_instance, add_edge_graph; simpl.
  split.
  - intros [Hx | [Hx | Hx]]; subst; auto.
  - intros [Hx | [Hx | Hx]]; subst; auto.
Qed.

Lemma add_edge_graph_evalid :
  forall g u v e a,
    vvalid g u ->
    vvalid g v ->
    ~ evalid g e ->
    evalid (add_edge_graph g u v e) a <-> evalid g a \/ a = e.
Proof.
  intros g u v e a Hu Hv Hne.
  unfold evalid, graph_instance, add_edge_graph; simpl.
  split.
  - intros [Ha | Ha]; [right; symmetry; exact Ha | left; exact Ha].
  - intros [Ha | Ha]; [right; exact Ha | left; symmetry; exact Ha].
Qed.

Lemma add_edge_graph_step :
  forall g u v e x y a,
    gvalid g ->
    vvalid g u ->
    vvalid g v ->
    ~ evalid g e ->
    step_aux (add_edge_graph g u v e) a x y <->
      step_aux g a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hu Hv Hne.
  unfold step_aux, graph_instance, graph_step,
    edge_endpoints_valid, edge_src, edge_dst, add_edge_graph.
  simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [left; reflexivity|].
        split.
        -- destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Heq | Hold] [_ Hxy]].
      { exfalso. apply Ha. symmetry; exact Heq. }
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [right; exact Hea|].
      split.
      * destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
        destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
Qed.

Lemma add_edge_graph_evalid_any :
  forall g u v e a,
    evalid (add_edge_graph g u v e) a <-> evalid g a \/ a = e.
Proof.
  intros g u v e a.
  unfold evalid, graph_instance, add_edge_graph; simpl.
  split.
  - intros [Ha | Ha]; [right; symmetry; exact Ha | left; exact Ha].
  - intros [Ha | Ha]; [right; exact Ha | left; symmetry; exact Ha].
Qed.

Lemma add_edge_graph_step_any :
  forall g u v e x y a,
    gvalid g ->
    ~ evalid g e ->
    step_aux (add_edge_graph g u v e) a x y <->
      step_aux g a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hne.
  unfold step_aux, graph_instance, graph_step,
    edge_endpoints_valid, edge_src, edge_dst, add_edge_graph.
  simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [left; reflexivity|].
        split.
        -- destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Heq | Hold] [_ Hxy]].
      { exfalso. apply Ha. symmetry; exact Heq. }
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [right; exact Hea|].
      split.
      * destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
        destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
Qed.

Lemma add_edge_graph_addEdge_any :
  forall g u v e,
    gvalid g ->
    ~ evalid g e ->
    addEdge g (add_edge_graph g u v e) u v e.
Proof.
  intros g u v e Hg Hne.
  constructor.
  - intros x. apply add_edge_graph_vvalid.
  - intros a. apply add_edge_graph_evalid_any.
  - intros x y a. apply add_edge_graph_step_any; auto.
Qed.

Lemma add_edge_graph_gvalid_new_vertex :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ vvalid g v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hvout.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold graph_step, edge_endpoints_valid, edge_src, edge_dst,
      add_edge_graph, graph_instance.
    simpl.
    destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
    split; [left; reflexivity |].
    split; [split; simpl; auto | left; split; reflexivity].
  - destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq].
    + subst a.
      exists u, v.
      unfold graph_step, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance.
      simpl.
      destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
      split; [left; reflexivity |].
      split; [split; simpl; auto | left; split; reflexivity].
    + specialize (Hg a Ha_old) as [x [y Hstep]].
      exists x, y.
      destruct Hstep as [_ [Hends Hxy]].
      unfold graph_step, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance in *.
      simpl in *.
      destruct (Z.eq_dec a e) as [Ha_eq' | _]; [contradiction |].
      split; [right; exact Ha_old |].
      destruct Hends as [Hsrc Hdst].
      split; [split; simpl; auto | exact Hxy].
Qed.

Lemma add_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    vvalid g v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hv.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
      edge_src, edge_dst, add_edge_graph.
    simpl.
    destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
    split; [left; reflexivity |].
    split; [split; simpl; auto | left; split; reflexivity].
  - destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq].
    + subst a.
      exists u, v.
      unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
        edge_src, edge_dst, add_edge_graph.
      simpl.
      destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
      split; [left; reflexivity |].
      split; [split; simpl; auto | left; split; reflexivity].
    + specialize (Hg a Ha_old) as [x [y Hstep]].
      exists x, y.
      destruct Hstep as [_ [Hends Hxy]].
      unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
        edge_src, edge_dst, add_edge_graph in *.
      simpl in *.
      destruct (Z.eq_dec a e) as [Ha_eq' | _]; [contradiction |].
      split; [right; exact Ha_old |].
      destruct Hends as [Hsrc Hdst].
      split; [split; simpl; auto | exact Hxy].
Qed.

Lemma remove_edge_graph_vvalid :
  forall g e x,
    vvalid (remove_edge_graph g e) x <-> vvalid g x.
Proof.
  intros g e x; reflexivity.
Qed.

Lemma remove_edge_graph_evalid :
  forall g e a,
    evalid (remove_edge_graph g e) a <-> evalid g a /\ a <> e.
Proof.
  intros g e a.
  unfold evalid, graph_instance, remove_edge_graph; simpl.
  split.
  - intros Hin.
    apply filter_In in Hin as [Hin Hfilter].
    destruct (Z.eq_dec a e) as [Ha | Ha]; [discriminate|].
    split; auto.
  - intros [Hin Hneq].
    apply filter_In.
    split; [exact Hin|].
    destruct (Z.eq_dec a e) as [Ha | Ha]; [contradiction|reflexivity].
Qed.

Lemma remove_edge_graph_step :
  forall g u v e x y a,
    gvalid g ->
    step_aux g e u v ->
    step_aux g a x y <->
      step_aux (remove_edge_graph g e) a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hstep.
  unfold step_aux, graph_instance, graph_step,
    edge_endpoints_valid, edge_src, edge_dst, remove_edge_graph.
  simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros Hcur.
      right; split; [reflexivity|].
      change (step_aux g e x y) in Hcur.
      pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hcur)
        as [[-> ->] | [-> ->]]; auto.
    + intros [Hremove | [_ Hxy]].
      * destruct Hremove as [Hin _].
        apply filter_In in Hin as [_ Hkeep].
        destruct (Z.eq_dec e e) as [_ | Hbad]; [discriminate | contradiction].
      * destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
        change (step_aux g e v u).
        apply step_sym; exact Hstep.
  - split.
    + intros [Hea [Hends Hxy]].
      left; split.
      * apply filter_In.
        split; [exact Hea |].
        destruct (Z.eq_dec a e) as [Heq | _]; [contradiction | reflexivity].
      * split; [exact Hends|exact Hxy].
    + intros [Hremove | [Heq _]]; [| contradiction].
      destruct Hremove as [Hin [Hends Hxy]].
      apply filter_In in Hin as [Hea _].
      split; [exact Hea | split; auto].
Qed.

Lemma remove_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    step_aux g e u v ->
    gvalid (remove_edge_graph g e).
Proof.
  intros g u v e Hg Hstep.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold remove_edge_graph in Ha; simpl in Ha.
  apply filter_In in Ha as [Ha Hkeep].
  destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq]; [discriminate|].
  destruct (Hg a Ha) as [x [y Hstep_a]].
  exists x, y.
  pose proof (proj1 (remove_edge_graph_step g u v e x y a Hg Hstep) Hstep_a)
    as [Hremove | [Ha_eq Hnew]].
  - exact Hremove.
  - contradiction.
Qed.

#[export] Instance addEdgeInSubgraph_instance :
  addEdgeInSubgraph G V E.
Proof.
  constructor.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hv Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid; auto.
    + split.
      * apply add_edge_graph_addEdge_any; auto.
      * constructor.
        -- intros z Hz.
           rewrite add_edge_graph_vvalid in Hz.
           destruct Hz as [Hz | [-> | ->]].
           ++ apply Hsub; exact Hz.
           ++ apply Hsub; exact Hu.
           ++ apply Hsub; exact Hv.
        -- intros x y a Ha.
           rewrite add_edge_graph_step_any in Ha by auto.
           destruct Ha as [Ha_old | [Ha_new Hxy]].
           ++ apply Hsub; exact Ha_old.
           ++ subst a.
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep |].
              apply step_sym; exact Hstep.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hvout Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid_new_vertex; auto.
    + split.
      * apply add_edge_graph_addEdge_any; auto.
      * constructor.
        -- intros z Hz.
           rewrite add_edge_graph_vvalid in Hz.
           destruct Hz as [Hz | [-> | ->]].
           ++ apply Hsub; exact Hz.
           ++ apply Hsub; exact Hu.
           ++ eapply step_vvalid2; eauto.
        -- intros x y a Ha.
           rewrite add_edge_graph_step_any in Ha by auto.
           destruct Ha as [Ha_old | [Ha_new Hxy]].
           ++ apply Hsub; exact Ha_old.
           ++ subst a.
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep |].
              apply step_sym; exact Hstep.
  - intros g h u v e Hg Hh Hsub Hu Hv He Hstep.
    exists (remove_edge_graph h e).
    split.
    + eapply remove_edge_graph_gvalid; eauto.
    + split.
      * constructor.
        -- intros z.
           rewrite remove_edge_graph_vvalid.
           split.
           ++ intros Hz; left; exact Hz.
           ++ intros [Hz | [-> | ->]]; auto.
        -- intros a.
           rewrite remove_edge_graph_evalid.
           split.
           ++ intros Ha.
              destruct (Z.eq_dec a e) as [-> | Hneq]; auto.
           ++ intros [[Ha _] | ->]; auto.
        -- intros x y a.
           apply remove_edge_graph_step; auto.
      * split.
        -- constructor.
           ++ intros z Hz.
              rewrite remove_edge_graph_vvalid in Hz.
              apply Hsub; exact Hz.
           ++ intros x y a Ha.
              apply Hsub.
              apply (proj2 (remove_edge_graph_step h u v e x y a Hh Hstep)).
              left; exact Ha.
        -- repeat split.
           ++ rewrite remove_edge_graph_vvalid; exact Hu.
           ++ rewrite remove_edge_graph_vvalid; exact Hv.
           ++ rewrite remove_edge_graph_evalid.
              intros [_ Hneq]; auto.
Qed.

#[export] Instance addEdgeGValid_instance :
  addEdgeGValid G V E.
Proof.
  constructor.
  intros g h u v e Hg Hadd.
  destruct Hadd as [_ Hadd_evalid Hadd_step].
  intros a Ha.
  apply Hadd_evalid in Ha as [Ha | ->].
  - destruct (Hg a Ha) as [x [y Hstep]].
    exists x, y.
    apply Hadd_step.
    left; exact Hstep.
  - exists u, v.
    apply Hadd_step.
    right; split; [reflexivity|auto].
Qed.


(** * Kruskal 抽象程序包装

    Kruskal 的抽象程序本身是 [whileP]，所以从任意中间状态继续执行时，
    仍然使用同一个 [Kruskal g]，不需要额外定义 [Kruskal_loop]。 *)

Definition graph_selectable_edge (g h : G) (e : E) : Prop :=
  evalid g e /\
  forall u v,
    step_aux g e u v ->
    ~ reachable h u v.

Definition forest_has_no_cycle (h : G) : Prop :=
  forall u,
    ~ exists p, is_simple_epath h u p u /\ p <> nil.

Definition forest_has_mst_extension (g h : G) : Prop :=
  exists y, is_mst g y /\ subgraph2 h y.

(** This is the cardinality/component law needed by the abstract while guard.
    It is stated for the multigraph model directly, without a [SimpleGraph]
    instance, so parallel input edges do not weaken the loop specification. *)
Definition kruskal_forest_progress_property (g : G) : Prop :=
  forall h,
    gvalid h ->
    forest_has_no_cycle h ->
    forest_has_mst_extension g h ->
    subgraph_vertex_eq h g ->
    ((exists e, graph_selectable_edge g h e) <->
     graph_edge_count h < graph_vertex_count g - 1).

Record KruskalEnv (g : G) : Prop := mkKruskalEnv {
  kruskal_graph_valid : gvalid g;
  kruskal_connected : connected g;
  kruskal_forest_progress : kruskal_forest_progress_property g;
}.

#[export] Instance initialForest_instance : Kruskal.initialForest G V E.
Proof.
  refine {|
    Kruskal.initial_forest := fun g =>
      mkG (graph_from g) (graph_to g) (graph_weight g)
          (graph_vertices g) nil
  |}.
  - intros g Hg.
    unfold gvalid, gvalid_instance, graph_wf. simpl. intros e [].
  - intros g v. simpl. tauto.
  - intros g e. simpl. tauto.
Defined.

Definition St : Type := @Kruskal.St G.

Definition initSt (g : G) : St :=
  @Kruskal.initSt G V E graph_instance gvalid_instance g
    initialForest_instance.

Definition initStPred (g : G) : St -> Prop :=
  fun s => s = initSt g.

Definition KruskalProg (g : G) : program St unit :=
  @Kruskal.Kruskal G V E graph_instance edge_weight_instance g.

Definition kruskal_state_is (s0 : St) : St -> Prop :=
  fun s => s = s0.

Definition kruskal_state_graph_matches (rg : G) : St -> Prop :=
  fun s => s.(Kruskal.graph_in_state) = rg.

Definition return_is_mst (g rg : G) : Prop :=
  is_mst g rg.

Lemma Kruskal_correct_concrete :
  forall g,
    KruskalEnv g ->
    Hoare (initStPred g) (KruskalProg g)
      (fun _ s => return_is_mst g s.(Kruskal.graph_in_state)).
Proof.
  intros g Henv.
  destruct Henv as [Hg Hconnected Hprogress].
  unfold initStPred, KruskalProg, initSt, return_is_mst.
  eapply (@Kruskal.Kruskal_correct
    G V E graph_instance gvalid_instance
    stepvalid_instance noempty_instance undirected_instance stepunique_instance
    elist_bijective_instance
    P path_instance emptypath_instance singlepath_instance concatpath_instance
    destruct1npath_instance
    edge_weight_instance
    g Hg Hconnected
    addEdgeInSubgraph_instance addEdgeGValid_instance
    tree_instance initialForest_instance).
Qed.

Definition growing_subgraph_steps
    (g : G) (s : St) : Prop :=
  forall e u v,
    step_aux s.(Kruskal.graph_in_state) e u v ->
    step_aux g e u v.

Definition state_selectable_edge (g : G) (s : St) (e : E) : Prop :=
  @Kruskal.selectable_edge G V E graph_instance g s e.

Lemma state_selectable_edge_graph :
  forall g s e,
    state_selectable_edge g s e <->
    graph_selectable_edge g s.(Kruskal.graph_in_state) e.
Proof.
  intros. reflexivity.
Qed.

Definition selected_edge_is_min_edge
    (g : G) (edge_order : list E) (i : Z) (s : St) (e : E) : Prop :=
  e = Znth i edge_order (-1) /\
  state_selectable_edge g s e /\
  min_object_of_subset Z_op_le
    (fun e' => state_selectable_edge g s e')
    (weight g) e.

Definition selected_edge_pair
    (g : G) (e : E) (u v : V) : Prop :=
  step_aux g e u v.

Definition selected_edge_add_to_mst
    (s s_next : St) (u v : V) (e : E) : Prop :=
  addEdge s.(Kruskal.graph_in_state) s_next.(Kruskal.graph_in_state) u v e.

Definition growing_subgraph_of (g : G) (s : St) : Prop :=
  (forall e,
    evalid s.(Kruskal.graph_in_state) e -> In e (graph_edges g)) /\
  growing_subgraph_steps g s.

(** * C 侧三数组排序模型

    [array_graph n m orig_u orig_v orig_w g] 永远描述原始输入构造的图。
    排序后的 C 数组不重新构造新图，而是通过 ghost [edge_order]
    说明“当前位置来自原始哪条边”。 *)

Definition edge_arrays_ordered_by
    (m : Z)
    (orig_u orig_v orig_w : list Z)
    (edge_u edge_v edge_w edge_order : list Z) : Prop :=
  Zlength orig_u = m /\
  Zlength orig_v = m /\
  Zlength orig_w = m /\
  Zlength edge_u = m /\
  Zlength edge_v = m /\
  Zlength edge_w = m /\
  Zlength edge_order = m /\
  Permutation edge_order (Zrange 0 m) /\
  (forall i, 0 <= i < m ->
    let e := Znth i edge_order (-1) in
    0 <= e < m /\
    Znth i edge_u 0 = Znth e orig_u 0 /\
    Znth i edge_v 0 = Znth e orig_v 0 /\
    Znth i edge_w 0 = Znth e orig_w 0).

Definition edge_arrays_sorted_by_weight
    (edge_w edge_order : list Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < Zlength edge_order ->
    Znth i edge_w 0 <= Znth j edge_w 0.

Definition after_sorted_edge_of_input
    (m : Z)
    (orig_u orig_v orig_w : list Z)
    (edge_u edge_v edge_w edge_order : list Z) : Prop :=
  edge_arrays_ordered_by m orig_u orig_v orig_w edge_u edge_v edge_w edge_order /\
  edge_arrays_sorted_by_weight edge_w edge_order.

(** ** 边表 quicksort 规格辅助谓词 *)

Definition same_outside_edge_arrays_range
    (edge_u edge_v edge_w edge_order : list Z)
    (edge_u' edge_v' edge_w' edge_order' : list Z)
    (left right : Z) : Prop :=
  forall i,
    0 <= i ->
    (i < left \/ right < i) ->
    Znth i edge_u 0 = Znth i edge_u' 0 /\
    Znth i edge_v 0 = Znth i edge_v' 0 /\
    Znth i edge_w 0 = Znth i edge_w' 0 /\
    Znth i edge_order (-1) = Znth i edge_order' (-1).

Definition edge_arrays_partitioned_by_weight_at
    (edge_w : list Z) (left right pivot : Z) : Prop :=
  left <= pivot <= right /\
  (forall i,
    left <= i < pivot ->
    Znth i edge_w 0 < Znth pivot edge_w 0) /\
  (forall i,
    pivot < i <= right ->
    Znth pivot edge_w 0 <= Znth i edge_w 0).

Definition edge_arrays_range_sorted_by_weight
    (edge_w : list Z) (left right : Z) : Prop :=
  forall i j,
    left <= i < j ->
    j <= right ->
    Znth i edge_w 0 <= Znth j edge_w 0.

(** * Kruskal 主循环扫描状态 *)

Definition uf_state_of (n : Z) (parents ranks : list Z) : uf_state :=
  {|
    uf_size := n;
    uf_parent := fun x =>
      if Z_le_dec 0 x then
        if Z_lt_dec x n then Znth x parents 0 else 0
      else 0;
    uf_rank := fun x =>
      if Z_le_dec 0 x then
        if Z_lt_dec x n then Znth x ranks 0 else 0
      else 0;
  |}.

Definition uf_parent_indices_valid (n : Z) (parents : list Z) : Prop :=
  forall x,
    0 <= x < n ->
    0 <= Znth x parents 0 < n.

Definition uf_rank_values_valid (n : Z) (ranks : list Z) : Prop :=
  forall x,
    0 <= x < n ->
    0 <= Znth x ranks 0.

Definition uf_initial (n : Z) (repr_of : Z -> Z) : Prop :=
  forall x, uf_domain n x -> repr_of x = x.

Definition uf_same_class (repr_of : Z -> Z) (x y : Z) : Prop :=
  same_class repr_of x y.

Definition uf_different_class (repr_of : Z -> Z) (x y : Z) : Prop :=
  repr_of x <> repr_of y.

Definition uf_merge
    (n : Z) (repr_of : Z -> Z) (x y : Z) (repr_of' : Z -> Z) : Prop :=
  0 <= x < n /\
  0 <= y < n /\
  merge (uf_domain n) repr_of x y repr_of'.

(* Supplied by the union-find module; Kruskal clients keep it abstract. *)
Parameter UF : Z -> Z -> (Z -> Z) -> Assertion.

Lemma uf_initial_identity :
  forall n,
    uf_initial n (fun x => x).
Proof.
  intros n x _. reflexivity.
Qed.

Lemma uf_same_class_iff_repr_eq :
  forall repr_of x y,
    uf_same_class repr_of x y <-> repr_of x = repr_of y.
Proof.
  intros. unfold uf_same_class, same_class. reflexivity.
Qed.

Lemma uf_different_class_iff_repr_neq :
  forall repr_of x y,
    uf_different_class repr_of x y <-> repr_of x <> repr_of y.
Proof.
  intros. unfold uf_different_class. reflexivity.
Qed.

Lemma uf_merge_domain_merge :
  forall n repr_of x y repr_of',
    uf_merge n repr_of x y repr_of' ->
    merge (uf_domain n) repr_of x y repr_of'.
Proof.
  intros n repr_of x y repr_of' [_ [_ Hmerge]].
  exact Hmerge.
Qed.

Definition output_edge_at
    (g : G) (s : St) (out_u out_v out_w : list Z) (i : Z) : Prop :=
  exists e,
    evalid s.(Kruskal.graph_in_state) e /\
    step_aux s.(Kruskal.graph_in_state) e (Znth i out_u 0) (Znth i out_v 0) /\
    weight g e = Some (Znth i out_w 0).

Definition output_prefix_matches_state
    (g : G) (chosen : Z)
    (out_u out_v out_w : list Z) (s : St) : Prop :=
  0 <= chosen /\
  Zlength out_u = chosen /\
  Zlength out_v = chosen /\
  Zlength out_w = chosen /\
  (forall i, 0 <= i < chosen ->
    output_edge_at g s out_u out_v out_w i) /\
  (forall e,
    evalid s.(Kruskal.graph_in_state) e ->
    exists i,
      0 <= i < chosen /\
      step_aux s.(Kruskal.graph_in_state) e (Znth i out_u 0) (Znth i out_v 0) /\
      weight g e = Some (Znth i out_w 0)).

Definition kruskal_result_graph_matches_array
    (ru rv rw : list Z) (g rg : G) : Prop :=
  0 <= Zlength (graph_vertices g) /\
  Zlength ru = Zlength (graph_vertices g) - 1 /\
  Zlength rv = Zlength (graph_vertices g) - 1 /\
  Zlength rw = Zlength (graph_vertices g) - 1 /\
  (forall i,
    In i (Zrange 0 (Zlength (graph_vertices g) - 1)) ->
    exists e,
      evalid rg e /\
      step_aux rg e (Znth i ru 0) (Znth i rv 0) /\
      weight g e = Some (Znth i rw 0)) /\
  (forall e,
    evalid rg e ->
    exists i,
      In i (Zrange 0 (Zlength (graph_vertices g) - 1)) /\
      step_aux rg e (Znth i ru 0) (Znth i rv 0) /\
      weight g e = Some (Znth i rw 0)).

Definition union_find_connectivity_matches_state
    (g : G) (s : St) (repr_of : Z -> Z) : Prop :=
  forall u v,
    In u (graph_vertices g) ->
    In v (graph_vertices g) ->
    (repr_of u = repr_of v <->
     reachable s.(Kruskal.graph_in_state) u v).

Definition scanned_prefix_not_selectable
    (g : G) (edge_order : list E) (i : Z) (s : St) : Prop :=
  forall k,
    0 <= k < i ->
    ~ state_selectable_edge g s (Znth k edge_order (-1)).

Definition kruskal_scan_phase
    (g : G) (s : St) (chosen : Z) : Prop :=
  0 <= chosen <= graph_vertex_count g - 1 /\
  ((exists e, state_selectable_edge g s e) <->
   chosen < graph_vertex_count g - 1).

(** The semantic Kruskal invariant.  Unlike the concrete scan bookkeeping,
    this records why the current forest can still be extended to an MST. *)
Definition kruskal_greedy_invariant (g : G) (s : St) : Prop :=
  forest_has_no_cycle s.(Kruskal.graph_in_state) /\
  forest_has_mst_extension g s.(Kruskal.graph_in_state) /\
  gvalid s.(Kruskal.graph_in_state) /\
  subgraph_vertex_eq s.(Kruskal.graph_in_state) g.

Lemma kruskal_scan_phase_from_greedy :
  forall g s chosen,
    KruskalEnv g ->
    kruskal_greedy_invariant g s ->
    chosen = graph_edge_count s.(Kruskal.graph_in_state) ->
    0 <= chosen <= graph_vertex_count g - 1 ->
    kruskal_scan_phase g s chosen.
Proof.
  intros g s chosen Henv Hgreedy Hchosen Hbounds.
  destruct Henv as [_ _ Hprogress].
  destruct Hgreedy as [Hacyclic [Hextension [Hvalid Hvertices]]].
  split; [exact Hbounds|].
  rewrite Hchosen.
  change
    ((exists e,
       graph_selectable_edge g s.(Kruskal.graph_in_state) e) <->
     graph_edge_count s.(Kruskal.graph_in_state) <
       graph_vertex_count g - 1).
  apply Hprogress; assumption.
Qed.

Lemma kruskal_scan_phase_complete :
  forall g s chosen,
    kruskal_scan_phase g s chosen ->
    chosen = graph_vertex_count g - 1 ->
    ~ exists e, state_selectable_edge g s e.
Proof.
  intros g s chosen [_ Hguard] Hchosen Hselectable.
  apply Hguard in Hselectable.
  lia.
Qed.

Definition kruskal_scan_state
    (g : G)
    (edge_order : list E)
    (i chosen : Z)
    (s : St) : Prop :=
  0 <= i <= graph_edge_count g /\
  kruskal_scan_phase g s chosen /\
  chosen = graph_edge_count s.(Kruskal.graph_in_state) /\
  growing_subgraph_of g s /\
  kruskal_greedy_invariant g s /\
  scanned_prefix_not_selectable g edge_order i s.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma Zlength_replace_Znth__partition_loop :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l as [| x xs IH]; simpl in *; intros n; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    rewrite IH. lia.
Qed.
Lemma replace_nth_app_r__partition_loop :
  forall {A : Type} n (a : A) (l1 l2 : list A),
    (n >= length l1)%nat ->
    replace_nth n (l1 ++ l2) a =
    replace_nth n l1 a ++ replace_nth (n - length l1) l2 a.
Proof.
  intros A n. induction n as [| n IH]; intros a l1 l2 Hlen.
  - destruct l1; simpl in *; try lia. reflexivity.
  - destruct l1; simpl in *; [reflexivity|].
    rewrite IH; auto; lia.
Qed.
Lemma replace_Znth_app_r__partition_loop :
  forall {A : Type} n (a : A) (l1 l2 : list A),
    n >= Zlength l1 ->
    replace_Znth n a (l1 ++ l2) =
    replace_Znth n a l1 ++ replace_Znth (n - Zlength l1) a l2.
Proof.
  intros A n a l1 l2 Hlen. unfold replace_Znth.
  rewrite Zlength_correct in *.
  replace (Z.to_nat (n - Z.of_nat (length l1)))
    with (Z.to_nat n - length l1)%nat by lia.
  rewrite replace_nth_app_r__partition_loop; auto; lia.
Qed.
Lemma replace_Znth_nothing__partition_loop :
  forall {A : Type} n (l : list A) (a : A),
    n >= Zlength l -> replace_Znth n a l = l.
Proof.
  intros A n l a Hlen. rewrite Zlength_correct in Hlen.
  unfold replace_Znth.
  assert (Hnat : (Z.to_nat n >= length l)%nat) by lia.
  clear Hlen. generalize dependent l.
  induction (Z.to_nat n) as [| m IH]; intros l Hnat.
  - destruct l; simpl in *; auto; lia.
  - destruct l; simpl in *; auto. rewrite IH; auto; lia.
Qed.
Lemma list_split_nth__partition_loop :
  forall (A : Type) (n : nat) (l : list A) (d : A),
    (n < length l)%nat ->
    l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  intros A n l d Hn. apply (firstn_skipSn d). exact Hn.
Qed.
Lemma swap_Znth_length__partition_loop :
  forall {A : Type} (l : list A) i j (d : A),
    Zlength (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)) = Zlength l.
Proof.
  intros.
  rewrite (Zlength_replace_Znth__partition_loop (replace_Znth i (Znth j l d) l)
    j (Znth i l d)).
  rewrite (Zlength_replace_Znth__partition_loop l i (Znth j l d)).
  reflexivity.
Qed.
Lemma swap_Znth_at_left__partition_loop :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l -> 0 <= j < Zlength l ->
    Znth i (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)) d = Znth j l d.
Proof.
  intros A l i j d Hi Hj.
  destruct (Z.eq_dec j i) as [-> | Hji].
  - repeat rewrite replace_Znth_Znth. reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
      by (try rewrite Zlength_replace_Znth__partition_loop; lia).
    rewrite Znth_replace_Znth_Same by lia. reflexivity.
Qed.
Lemma swap_Znth_at_right__partition_loop :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l -> 0 <= j < Zlength l ->
    Znth j (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)) d = Znth i l d.
Proof.
  intros A l i j d Hi Hj.
  rewrite Znth_replace_Znth_Same
    by (rewrite Zlength_replace_Znth__partition_loop; lia).
  reflexivity.
Qed.
Lemma swap_Znth_at_other__partition_loop :
  forall {A : Type} (l : list A) i j k (d : A),
    0 <= i < Zlength l -> 0 <= j < Zlength l ->
    0 <= k < Zlength l -> k <> i -> k <> j ->
    Znth k (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)) d = Znth k l d.
Proof.
  intros A l i j k d Hi Hj Hk Hki Hkj.
  rewrite Znth_replace_Znth_Diff with (i := j) (j := k)
    by (try rewrite Zlength_replace_Znth__partition_loop; lia).
  rewrite Znth_replace_Znth_Diff with (i := i) (j := k) by lia.
  reflexivity.
Qed.
Lemma Znth_overflow__partition_loop :
  forall {A : Type} (l : list A) k (d : A),
    Zlength l <= k -> Znth k l d = d.
Proof.
  intros A l k d Hk. unfold Znth. apply nth_overflow.
  rewrite Zlength_correct in Hk. lia.
Qed.
Lemma swap_Znth_at_other_nonnegative__partition_loop :
  forall {A : Type} (l : list A) i j k (d : A),
    0 <= i < Zlength l -> 0 <= j < Zlength l -> 0 <= k ->
    k <> i -> k <> j ->
    Znth k (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)) d = Znth k l d.
Proof.
  intros A l i j k d Hi Hj Hk Hki Hkj.
  destruct (Z_lt_ge_dec k (Zlength l)) as [Hlt | Hge].
  - apply swap_Znth_at_other__partition_loop; lia.
  - rewrite Znth_overflow__partition_loop by
      (rewrite swap_Znth_length__partition_loop; lia).
    rewrite Znth_overflow__partition_loop by lia. reflexivity.
Qed.
Lemma replace_Znth_swap_form__partition_loop :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros. assert (Hlen2 : 0 <= Zlength l2) by (rewrite Zlength_correct; lia).
  set (n1 := Zlength l1). set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r__partition_loop with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3)
    by (subst n1; lia).
  rewrite (replace_Znth_nothing__partition_loop (A := A) n1 l1 xj)
    by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia). simpl.
  rewrite replace_Znth_app_r__partition_loop with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3)
    by (subst n2; lia).
  rewrite (replace_Znth_nothing__partition_loop (A := A)
    (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r__partition_loop with
    (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing__partition_loop (A := A)
    (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia. reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__partition_loop :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i -> i < j -> j < Zlength l ->
    Permutation l (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hij Hj.
  remember (Znth i l d) as xi. remember (Znth j l d) as xj.
  set (ni := Z.to_nat i). set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l). set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr). set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi :: lr).
  { subst l1 lr ni.
    rewrite (list_split_nth__partition_loop _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj; lia. }
    rewrite Heqxi. reflexivity. }
  assert (Hj_lr : (nj < length lr)%nat).
  { subst nj lr ni. rewrite length_skipn. rewrite Zlength_correct in Hj. lia. }
  assert (Hsplit_j : lr = l2 ++ xj :: l3).
  { subst l2 l3.
    rewrite (list_split_nth__partition_loop _ nj lr d) at 1 by exact Hj_lr.
    replace xj with (nth nj lr d).
    2:{ subst nj lr ni. rewrite Heqxj. unfold Znth. rewrite nth_skipn.
        assert (Hnat : (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
        { apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
          repeat rewrite Z2Nat.id by lia. lia. }
        rewrite Nat.add_comm, Hnat. reflexivity. }
    reflexivity. }
  assert (Hl : l = l1 ++ xi :: l2 ++ xj :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi :: l2 ++ xj :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{ subst l1 ni. rewrite Zlength_correct, length_firstn.
      rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia. }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{ subst l1 l2 lr ni nj. rewrite !Zlength_correct, !length_firstn,
        length_skipn. rewrite Zlength_correct in Hj. lia. }
  rewrite replace_Znth_swap_form__partition_loop.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma replace_nth_comm_any__partition_loop :
  forall {A : Type} ni nj (l : list A) (a b : A),
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni. induction ni as [| ni IH]; intros nj l a b Hneq;
    destruct l as [| x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl; [contradiction Hneq; reflexivity | reflexivity].
  - destruct nj; reflexivity.
  - destruct nj; simpl; [reflexivity |].
    f_equal. apply IH. intros Heq. apply Hneq. now f_equal.
Qed.
Lemma permutation_swap_Znth__partition_loop :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l -> 0 <= j < Zlength l ->
    Permutation l (replace_Znth j (Znth i l d)
      (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hij].
  - apply permutation_swap_Znth_lt__partition_loop; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + assert (Hcomm : forall (a b : A),
        replace_Znth j b (replace_Znth i a l) =
        replace_Znth i a (replace_Znth j b l)).
      { intros a b. unfold replace_Znth.
        apply replace_nth_comm_any__partition_loop. intro Hnat.
        apply Z2Nat.inj in Hnat; lia. }
      rewrite Hcomm.
      apply permutation_swap_Znth_lt__partition_loop; lia.
    + assert (i = j) by lia. subst j.
      repeat rewrite replace_Znth_Znth. apply Permutation_refl.
Qed.
Lemma edge_arrays_ordered_swap_positions__partition_loop :
  forall m orig_u orig_v orig_w edge_u edge_v edge_w edge_order i j,
    edge_arrays_ordered_by m orig_u orig_v orig_w
      edge_u edge_v edge_w edge_order ->
    0 <= i < m -> 0 <= j < m ->
    edge_arrays_ordered_by m orig_u orig_v orig_w
      (replace_Znth j (Znth i edge_u 0) (replace_Znth i (Znth j edge_u 0) edge_u))
      (replace_Znth j (Znth i edge_v 0) (replace_Znth i (Znth j edge_v 0) edge_v))
      (replace_Znth j (Znth i edge_w 0) (replace_Znth i (Znth j edge_w 0) edge_w))
      (replace_Znth j (Znth i edge_order (-1))
        (replace_Znth i (Znth j edge_order (-1)) edge_order)).
Proof.
  intros m ou ov ow eu ev ew eo i j Hord Hi Hj.
  destruct Hord as [Hou [Hov [How [Heu [Hev [Hew [Heo [Hperm Hmap]]]]]]]].
  split; [exact Hou|]. split; [exact Hov|]. split; [exact How|].
  split; [rewrite swap_Znth_length__partition_loop; exact Heu|].
  split; [rewrite swap_Znth_length__partition_loop; exact Hev|].
  split; [rewrite swap_Znth_length__partition_loop; exact Hew|].
  split; [rewrite swap_Znth_length__partition_loop; exact Heo|].
  split.
  - eapply Permutation_trans.
    + apply Permutation_sym. apply permutation_swap_Znth__partition_loop; lia.
    + exact Hperm.
  - intros k Hk. destruct (Z.eq_dec k i) as [-> | Hki].
    + repeat rewrite swap_Znth_at_left__partition_loop by lia. apply Hmap; lia.
    + destruct (Z.eq_dec k j) as [-> | Hkj].
      * repeat rewrite swap_Znth_at_right__partition_loop by lia. apply Hmap; lia.
      * repeat rewrite swap_Znth_at_other__partition_loop by lia. apply Hmap; lia.
Qed.
Lemma same_outside_edge_arrays_range_swap_inside__partition_loop :
  forall bu bv bw bo cu cv cw co left right i j,
    same_outside_edge_arrays_range bu bv bw bo cu cv cw co left right ->
    Zlength cu = Zlength cv -> Zlength cv = Zlength cw ->
    Zlength cw = Zlength co ->
    0 <= i < Zlength cu -> 0 <= j < Zlength cu ->
    left <= i <= right -> left <= j <= right ->
    same_outside_edge_arrays_range bu bv bw bo
      (replace_Znth j (Znth i cu 0) (replace_Znth i (Znth j cu 0) cu))
      (replace_Znth j (Znth i cv 0) (replace_Znth i (Znth j cv 0) cv))
      (replace_Znth j (Znth i cw 0) (replace_Znth i (Znth j cw 0) cw))
      (replace_Znth j (Znth i co (-1)) (replace_Znth i (Znth j co (-1)) co))
      left right.
Proof.
  intros bu bv bw bo cu cv cw co left right i j Hsame Huv Hvw Hwo
    Hi Hj Hii Hjj k Hk Hout.
  specialize (Hsame k Hk Hout).
  destruct Hsame as [Hu [Hv [Hw Ho]]].
  repeat split.
  - rewrite swap_Znth_at_other_nonnegative__partition_loop by lia. exact Hu.
  - rewrite swap_Znth_at_other_nonnegative__partition_loop by lia. exact Hv.
  - rewrite swap_Znth_at_other_nonnegative__partition_loop by lia. exact Hw.
  - rewrite swap_Znth_at_other_nonnegative__partition_loop by lia. exact Ho.
Qed.
Lemma partition_scan_swap__partition_loop :
  forall w left right pivot i j,
    0 <= left -> left <= i <= j -> j < right -> right < Zlength w ->
    Znth j w 0 < pivot -> Znth right w 0 = pivot ->
    (forall k, left <= k < i -> Znth k w 0 < pivot) ->
    (forall k, i <= k < j -> pivot <= Znth k w 0) ->
    let w' := replace_Znth j (Znth i w 0)
      (replace_Znth i (Znth j w 0) w) in
    (forall k, left <= k < i + 1 -> Znth k w' 0 < pivot) /\
    (forall k, i + 1 <= k < j + 1 -> pivot <= Znth k w' 0) /\
    Znth right w' 0 = pivot.
Proof.
  intros w left right pivot i j Hleft Hij Hjright Hrightlen Hjlt Hp Hlo Hhi w'.
  assert (Hi : 0 <= i < Zlength w) by lia.
  assert (Hj : 0 <= j < Zlength w) by lia.
  assert (Hr : 0 <= right < Zlength w) by lia.
  split.
  - intros k Hk. destruct (Z.eq_dec k i) as [-> | Hki].
    + unfold w'. rewrite swap_Znth_at_left__partition_loop by lia. exact Hjlt.
    + unfold w'. rewrite swap_Znth_at_other__partition_loop by lia. apply Hlo; lia.
  - split.
    + intros k Hk. destruct (Z.eq_dec k j) as [-> | Hkj].
      * unfold w'. rewrite swap_Znth_at_right__partition_loop by lia.
        destruct (Z.eq_dec i j) as [-> | Hneq]; [lia|]. apply Hhi; lia.
      * unfold w'. rewrite swap_Znth_at_other__partition_loop by lia. apply Hhi; lia.
    + unfold w'. rewrite swap_Znth_at_other__partition_loop by lia. exact Hp.
Qed.
Lemma partition_scan_step__partition_loop :
  forall (w : list Z) (left right pivot i j : Z),
    i <= j -> j < right ->
    pivot <= Znth j w 0 ->
    (forall k, i <= k < j -> pivot <= Znth k w 0) ->
    forall k, i <= k < j + 1 -> pivot <= Znth k w 0.
Proof.
  intros w left right pivot i j Hij Hjr Hcur Hband k Hk.
  destruct (Z.eq_dec k j) as [-> | Hneq]; [exact Hcur|].
  apply Hband; lia.
Qed.
Lemma partition_finish_swap__partition_loop :
  forall w left right pivot i,
    0 <= left -> left <= i <= right -> right < Zlength w ->
    Znth right w 0 = pivot ->
    (forall k, left <= k < i -> Znth k w 0 < pivot) ->
    (forall k, i <= k < right -> pivot <= Znth k w 0) ->
    edge_arrays_partitioned_by_weight_at
      (replace_Znth right (Znth i w 0)
        (replace_Znth i (Znth right w 0) w)) left right i.
Proof.
  intros w left right pivot i Hleft Hi Hright Hp Hlo Hhi.
  assert (Hir : 0 <= i < Zlength w) by lia.
  assert (Hrr : 0 <= right < Zlength w) by lia.
  unfold edge_arrays_partitioned_by_weight_at. split; [lia|]. split.
  - intros k Hk.
    rewrite (swap_Znth_at_other__partition_loop w i right k 0) by lia.
    rewrite (swap_Znth_at_left__partition_loop w i right 0) by lia.
    rewrite Hp.
    apply Hlo; lia.
  - intros k Hk.
    destruct (Z.eq_dec k right) as [-> | Hneq].
    + rewrite (swap_Znth_at_right__partition_loop w i right 0) by lia.
      rewrite (swap_Znth_at_left__partition_loop w i right 0) by lia.
      rewrite Hp.
      apply Hhi; lia.
    + rewrite (swap_Znth_at_other__partition_loop w i right k 0) by lia.
      rewrite (swap_Znth_at_left__partition_loop w i right 0) by lia.
      rewrite Hp.
      apply Hhi; lia.
Qed.
Lemma same_outside_edge_arrays_range_trans__quicksort_results :
  forall au av aw ao bu bv bw bo cu cv cw co du dv dw do_ left right pivot,
    left <= pivot <= right ->
    same_outside_edge_arrays_range
      au av aw ao bu bv bw bo left right ->
    same_outside_edge_arrays_range
      bu bv bw bo cu cv cw co left (pivot - 1) ->
    same_outside_edge_arrays_range
      cu cv cw co du dv dw do_ (pivot + 1) right ->
    same_outside_edge_arrays_range
      au av aw ao du dv dw do_ left right.
Proof.
  unfold same_outside_edge_arrays_range.
  intros au av aw ao bu bv bw bo cu cv cw co du dv dw do_
    left right pivot Hpivot Hab Hbc Hcd i Hi Houtside.
  specialize (Hab i Hi Houtside).
  assert (Houtside_bc : i < left \/ pivot - 1 < i)
    by (destruct Houtside; [left | right]; lia).
  assert (Houtside_cd : i < pivot + 1 \/ right < i)
    by (destruct Houtside; [left | right]; lia).
  specialize (Hbc i Hi Houtside_bc).
  specialize (Hcd i Hi Houtside_cd).
  destruct Hab as [Habu [Habv [Habw Habo]]].
  destruct Hbc as [Hbcu [Hbcv [Hbcw Hbco]]].
  destruct Hcd as [Hcdu [Hcdv [Hcdw Hcdo]]].
  repeat split; congruence.
Qed.
Lemma edge_arrays_range_sorted_vacuous__quicksort_results :
  forall edge_w left right,
    right <= left ->
    edge_arrays_range_sorted_by_weight edge_w left right.
Proof.
  unfold edge_arrays_range_sorted_by_weight.
  intros edge_w left right Hempty i j Hij Hj.
  lia.
Qed.
Lemma edge_arrays_sorted_full_range__quicksort_results :
  forall edge_w edge_order n,
    Zlength edge_order = n ->
    edge_arrays_range_sorted_by_weight edge_w 0 (n - 1) ->
    edge_arrays_sorted_by_weight edge_w edge_order.
Proof.
  unfold edge_arrays_range_sorted_by_weight,
    edge_arrays_sorted_by_weight.
  intros edge_w edge_order n Hlen Hsorted i j Hij Hj.
  apply Hsorted; lia.
Qed.
Lemma In_Znth_Zlength__quicksort_results :
  forall (A : Type) (l : list A) (x d : A),
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  pose proof (@In_nth A l x d Hin) as [i [Hi Hnth]].
  exists (Z.of_nat i).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma NoDup_Znth_inj__quicksort_results :
  forall (A : Type) (l : list A) (d : A) i j,
    NoDup l ->
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Znth i l d = Znth j l d ->
    i = j.
Proof.
  intros A l d i j Hnodup Hi Hj Heq.
  apply Z2Nat.inj; try lia.
  apply (proj1 (NoDup_nth l d) Hnodup).
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - exact Heq.
Qed.
Lemma edge_arrays_range_values_preserved__quicksort_results :
  forall n orig_u orig_v orig_w
    old_u old_v old_w old_order new_u new_v new_w new_order
    left right j,
    edge_arrays_ordered_by n orig_u orig_v orig_w
      old_u old_v old_w old_order ->
    edge_arrays_ordered_by n orig_u orig_v orig_w
      new_u new_v new_w new_order ->
    Permutation old_order new_order ->
    same_outside_edge_arrays_range
      old_u old_v old_w old_order new_u new_v new_w new_order left right ->
    0 <= left ->
    right < n ->
    left <= j <= right ->
    exists k, left <= k <= right /\ Znth j new_w 0 = Znth k old_w 0.
Proof.
  intros n orig_u orig_v orig_w
    old_u old_v old_w old_order new_u new_v new_w new_order
    left right j Hold Hnew Hperm Houtside Hleft Hright Hj.
  unfold edge_arrays_ordered_by in Hold, Hnew.
  destruct Hold as
    [Hou [Hov [How [Hol_u [Hol_v [Hol_w [Hol_o [Hold_range Hold_at]]]]]]]].
  destruct Hnew as
    [Hnu [Hnv [Hnw [Hnl_u [Hnl_v [Hnl_w [Hnl_o [Hnew_range Hnew_at]]]]]]]].
  assert (Hj_bounds : 0 <= j < n) by lia.
  specialize (Hnew_at j Hj_bounds).
  cbn in Hnew_at.
  destruct Hnew_at as [He_bounds [Hnew_u [Hnew_v Hnew_w_at]]].
  assert (Hin_new : In (Znth j new_order (-1)) new_order).
  { apply Znth_In_Zlength. rewrite Hnl_o. exact Hj_bounds. }
  assert (Hin_old : In (Znth j new_order (-1)) old_order).
  { eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hin_new. }
  destruct (In_Znth_Zlength__quicksort_results
    Z old_order (Znth j new_order (-1)) (-1) Hin_old)
    as [k [Hk_bounds Hk_edge]].
  rewrite Hol_o in Hk_bounds.
  assert (Hk_range : left <= k <= right).
  { destruct (Z_lt_ge_dec k left) as [Hkl | Hlk]; [|].
    - exfalso.
      specialize (Houtside k ltac:(lia) ltac:(left; lia)).
      destruct Houtside as [_ [_ [_ Houtside_order]]].
      assert (Hnew_nodup : NoDup new_order).
      { eapply Permutation_NoDup.
        - apply Permutation_sym. exact Hnew_range.
        - apply NoDup_Zrange. }
      assert (Hkj : k = j).
      { eapply NoDup_Znth_inj__quicksort_results.
        - exact Hnew_nodup.
        - rewrite Hnl_o. lia.
        - rewrite Hnl_o. lia.
        - rewrite <- Houtside_order. exact Hk_edge. }
      lia.
    - destruct (Z_le_gt_dec k right) as [Hkr | Hrk]; [lia |].
      exfalso.
      specialize (Houtside k ltac:(lia) ltac:(right; lia)).
      destruct Houtside as [_ [_ [_ Houtside_order]]].
      assert (Hnew_nodup : NoDup new_order).
      { eapply Permutation_NoDup.
        - apply Permutation_sym. exact Hnew_range.
        - apply NoDup_Zrange. }
      assert (Hkj : k = j).
      { eapply NoDup_Znth_inj__quicksort_results.
        - exact Hnew_nodup.
        - rewrite Hnl_o. lia.
        - rewrite Hnl_o. lia.
        - rewrite <- Houtside_order. exact Hk_edge. }
      lia. }
  specialize (Hold_at k Hk_bounds).
  cbn in Hold_at.
  destruct Hold_at as [Hke_bounds [Hold_u [Hold_v Hold_w_at]]].
  exists k. split; [exact Hk_range |].
  rewrite Hnew_w_at, Hold_w_at, Hk_edge.
  reflexivity.
Qed.
Lemma edge_arrays_range_sorted_join__quicksort_results :
  forall n orig_u orig_v orig_w
    bu bv bw bo cu cv cw co du dv dw do_ left right pivot,
    edge_arrays_ordered_by n orig_u orig_v orig_w bu bv bw bo ->
    edge_arrays_ordered_by n orig_u orig_v orig_w cu cv cw co ->
    edge_arrays_ordered_by n orig_u orig_v orig_w du dv dw do_ ->
    Permutation bo co ->
    Permutation co do_ ->
    same_outside_edge_arrays_range
      bu bv bw bo cu cv cw co left (pivot - 1) ->
    same_outside_edge_arrays_range
      cu cv cw co du dv dw do_ (pivot + 1) right ->
    edge_arrays_range_sorted_by_weight cw left (pivot - 1) ->
    edge_arrays_range_sorted_by_weight dw (pivot + 1) right ->
    edge_arrays_partitioned_by_weight_at bw left right pivot ->
    0 <= left ->
    right < n ->
    edge_arrays_range_sorted_by_weight dw left right.
Proof.
  intros n orig_u orig_v orig_w
    bu bv bw bo cu cv cw co du dv dw do_ left right pivot
    Hbord Hcord Hdord Hperm_bc Hperm_cd Houtside_bc Houtside_cd
    Hsorted_c Hsorted_d Hpartition Hleft Hright.
  unfold edge_arrays_partitioned_by_weight_at in Hpartition.
  destruct Hpartition as [Hpivot [Hlower Hupper]].
  unfold edge_arrays_range_sorted_by_weight.
  intros i j Hij Hj.
  assert (Hi0 : 0 <= i) by lia.
  assert (Hj0 : 0 <= j) by lia.
  destruct (Z_lt_ge_dec j pivot) as [Hjp | Hpj_ge].
  - specialize (Hsorted_c i j ltac:(lia) ltac:(lia)).
    pose proof (Houtside_cd i Hi0 ltac:(left; lia)) as Hcd_i.
    pose proof (Houtside_cd j Hj0 ltac:(left; lia)) as Hcd_j.
    destruct Hcd_i as [Hcdu_i [Hcdv_i [Hcdw_i Hcdo_i]]].
    destruct Hcd_j as [Hcdu_j [Hcdv_j [Hcdw_j Hcdo_j]]].
    rewrite <- Hcdw_i, <- Hcdw_j.
    exact Hsorted_c.
  - destruct (Z.eq_dec j pivot) as [Hjeq | Hjneq].
    + subst j.
      destruct (edge_arrays_range_values_preserved__quicksort_results
        n orig_u orig_v orig_w bu bv bw bo cu cv cw co
        left (pivot - 1) i Hbord Hcord Hperm_bc Houtside_bc
        Hleft ltac:(lia) ltac:(lia)) as [k [Hk Hweight_i]].
      specialize (Hlower k ltac:(lia)).
      pose proof (Houtside_bc pivot ltac:(lia) ltac:(right; lia)) as Hbc_p.
      pose proof (Houtside_cd i Hi0 ltac:(left; lia)) as Hcd_i.
      pose proof (Houtside_cd pivot ltac:(lia) ltac:(left; lia)) as Hcd_p.
      destruct Hbc_p as [_ [_ [Hbcw_p _]]].
      destruct Hcd_i as [_ [_ [Hcdw_i _]]].
      destruct Hcd_p as [_ [_ [Hcdw_p _]]].
      rewrite <- Hcdw_i, Hweight_i, <- Hcdw_p, <- Hbcw_p.
      lia.
    + assert (Hpj : pivot < j) by lia.
      destruct (Z_lt_ge_dec i pivot) as [Hip | Hpi_ge].
      { destruct (edge_arrays_range_values_preserved__quicksort_results
        n orig_u orig_v orig_w bu bv bw bo cu cv cw co
        left (pivot - 1) i Hbord Hcord Hperm_bc Houtside_bc
        Hleft ltac:(lia) ltac:(lia)) as [ki [Hki Hweight_i]].
      destruct (edge_arrays_range_values_preserved__quicksort_results
        n orig_u orig_v orig_w cu cv cw co du dv dw do_
        (pivot + 1) right j Hcord Hdord Hperm_cd Houtside_cd
        ltac:(lia) Hright ltac:(lia)) as [kj [Hkj Hweight_j]].
      specialize (Hlower ki ltac:(lia)).
      specialize (Hupper kj ltac:(lia)).
      pose proof (Houtside_bc pivot ltac:(lia) ltac:(right; lia)) as Hbc_p.
      pose proof (Houtside_bc kj ltac:(lia) ltac:(right; lia)) as Hbc_kj.
      pose proof (Houtside_cd i Hi0 ltac:(left; lia)) as Hcd_i.
      destruct Hbc_p as [_ [_ [Hbcw_p _]]].
      destruct Hbc_kj as [_ [_ [Hbcw_kj _]]].
      destruct Hcd_i as [_ [_ [Hcdw_i _]]].
      rewrite <- Hcdw_i, Hweight_i, Hweight_j, <- Hbcw_kj.
      lia. }
      destruct (Z.eq_dec i pivot) as [Hieq | Hineq].
      { subst i.
        destruct (edge_arrays_range_values_preserved__quicksort_results
          n orig_u orig_v orig_w cu cv cw co du dv dw do_
          (pivot + 1) right j Hcord Hdord Hperm_cd Houtside_cd
          ltac:(lia) Hright ltac:(lia)) as [k [Hk Hweight_j]].
        specialize (Hupper k ltac:(lia)).
        pose proof (Houtside_bc pivot ltac:(lia) ltac:(right; lia)) as Hbc_p.
        pose proof (Houtside_bc k ltac:(lia) ltac:(right; lia)) as Hbc_k.
        pose proof (Houtside_cd pivot ltac:(lia) ltac:(left; lia)) as Hcd_p.
        destruct Hbc_p as [_ [_ [Hbcw_p _]]].
        destruct Hbc_k as [_ [_ [Hbcw_k _]]].
        destruct Hcd_p as [_ [_ [Hcdw_p _]]].
        rewrite <- Hcdw_p, <- Hbcw_p, Hweight_j, <- Hbcw_k.
        exact Hupper. }
      assert (Hpi : pivot < i) by lia.
      apply Hsorted_d; lia.
Qed.
Lemma uf_path_compress_preserves_abstract__find_root :
  forall s repr_of x,
    uf_abstract s repr_of ->
    valid s x ->
    uf_parent s x <> x ->
    uf_abstract
      (set_parent_state x (uf_parent s (uf_parent s x)) s) repr_of.
Proof.
  intros s repr_of x Habs Hvalidx Hx_nonroot.
  destruct Habs as [Hlegal [Hinv [Hmodels Hrank_bound]]].
  pose proof (uf_inv_parent_closed s Hinv x Hvalidx) as Hvalid_parent.
  pose proof
    (uf_inv_parent_closed s Hinv (uf_parent s x) Hvalid_parent)
    as Hvalid_grandparent.
  assert (Hgrandparent_chain :
    forall z r,
      parent_chain s z r ->
      uf_parent s r = r ->
      parent_chain
        (set_parent_state x (uf_parent s (uf_parent s x)) s) z r).
  {
    intros z r Hchain Hroot.
    induction Hchain as
      [z Hvalidz | z y r Hvalidz Hzy Hchain IH].
    - apply parent_chain_refl.
      apply (proj2
        (valid_set_parent_state s x (uf_parent s (uf_parent s x)) z)).
      exact Hvalidz.
    - destruct (Z.eq_dec z x) as [-> | Hzx].
      + assert (Hyx : y <> x) by congruence.
        assert (Hrx : r <> x) by congruence.
        assert (Hroot_new :
          uf_parent
            (set_parent_state x (uf_parent s (uf_parent s x)) s) r = r).
        {
          rewrite uf_parent_set_parent_neq by exact Hrx.
          exact Hroot.
        }
        destruct (Z.eq_dec (uf_parent s y) y) as [Hyroot | Hy_nonroot].
        * assert (y = r).
          {
            eapply parent_chain_root_unique.
            - apply parent_chain_refl. rewrite <- Hzy. exact Hvalid_parent.
            - exact Hyroot.
            - exact Hchain.
            - exact Hroot.
          }
          assert (Hparent_x_r : uf_parent s x = r) by congruence.
          subst y.
          eapply parent_chain_step.
          -- apply (proj2
               (valid_set_parent_state s x
                 (uf_parent s (uf_parent s x)) x)).
             exact Hvalidx.
          -- rewrite uf_parent_set_parent_eq, Hparent_x_r, Hroot.
             reflexivity.
          -- apply parent_chain_refl.
             apply (proj2
               (valid_set_parent_state s x
                 (uf_parent s (uf_parent s x)) r)).
             eapply parent_chain_valid_end; eauto.
        * pose proof
            (root_chain_tail
              (set_parent_state x (uf_parent s (uf_parent s x)) s)
              y r (IH Hroot) Hroot_new) as Htail_new.
          assert (Hparent_new_nonroot :
            uf_parent
              (set_parent_state x (uf_parent s (uf_parent s x)) s) y <> y).
          {
            rewrite uf_parent_set_parent_neq by exact Hyx.
            exact Hy_nonroot.
          }
          specialize (Htail_new Hparent_new_nonroot).
          rewrite uf_parent_set_parent_neq in Htail_new by exact Hyx.
          eapply parent_chain_step.
          -- apply (proj2
               (valid_set_parent_state s x
                 (uf_parent s (uf_parent s x)) x)).
             exact Hvalidx.
          -- rewrite uf_parent_set_parent_eq, Hzy.
             reflexivity.
          -- exact Htail_new.
      + eapply parent_chain_step.
        * apply (proj2
            (valid_set_parent_state s x
              (uf_parent s (uf_parent s x)) z)).
          exact Hvalidz.
        * rewrite uf_parent_set_parent_neq by exact Hzx.
          exact Hzy.
        * exact (IH Hroot).
  }
  split.
  - intros a Hva.
    apply Hlegal.
    apply (proj1
      (valid_set_parent_state s x (uf_parent s (uf_parent s x)) a)).
    exact Hva.
  - split.
    + split.
      * intros a Hva.
        destruct (Z.eq_dec a x) as [-> | Hax].
        -- rewrite uf_parent_set_parent_eq.
           exact Hvalid_grandparent.
        -- rewrite uf_parent_set_parent_neq by exact Hax.
           apply (proj2
             (valid_set_parent_state s x
               (uf_parent s (uf_parent s x)) (uf_parent s a))).
           apply (uf_inv_parent_closed s Hinv a).
           apply (proj1
             (valid_set_parent_state s x
               (uf_parent s (uf_parent s x)) a)).
           exact Hva.
      * split.
        -- intros a Hva.
           rewrite uf_rank_set_parent_state.
           apply (uf_inv_rank_nonnegative s Hinv a).
           apply (proj1
             (valid_set_parent_state s x
               (uf_parent s (uf_parent s x)) a)).
           exact Hva.
        -- intros a Hva Hneq.
           rewrite uf_rank_set_parent_state.
           destruct (Z.eq_dec a x) as [-> | Hax].
           ++ rewrite uf_parent_set_parent_eq.
              pose proof
                (uf_inv_rank_increases s Hinv x Hvalidx Hx_nonroot)
                as Hrank_parent.
              pose proof
                (uf_inv_rank_increases s Hinv (uf_parent s x)
                  Hvalid_parent) as Hrank_grandparent.
              destruct (Z.eq_dec (uf_parent s (uf_parent s x))
                (uf_parent s x)) as [Heq | Hne].
              ** rewrite Heq. exact Hrank_parent.
              ** specialize (Hrank_grandparent Hne).
                 exact (Z.lt_trans _ _ _ Hrank_parent Hrank_grandparent).
           ++ rewrite uf_parent_set_parent_neq by exact Hax.
              rewrite uf_rank_set_parent_state.
              apply (uf_inv_rank_increases s Hinv a).
              ** apply (proj1
                   (valid_set_parent_state s x
                     (uf_parent s (uf_parent s x)) a)).
                 exact Hva.
              ** intro Ha.
                 apply Hneq.
                 rewrite uf_parent_set_parent_neq by exact Hax.
                 exact Ha.
    + split.
      * intros a Hva.
        pose proof (proj1
          (valid_set_parent_state s x (uf_parent s (uf_parent s x)) a)
          Hva) as Hva_old.
        destruct (Hmodels a Hva_old) as
          [_ [Hchain [Hvalid_repr Hroot_repr]]].
        split.
        -- exact Hva.
        -- split.
           ++ apply Hgrandparent_chain; assumption.
           ++ split.
              ** apply (proj2
                   (valid_set_parent_state s x
                     (uf_parent s (uf_parent s x)) (repr_of a))).
                 exact Hvalid_repr.
              ** destruct (Z.eq_dec (repr_of a) x) as [Heq | Hneq].
                 --- subst x.
                     exfalso.
                     apply Hx_nonroot.
                     exact Hroot_repr.
                 --- rewrite uf_parent_set_parent_neq by exact Hneq.
                     exact Hroot_repr.
      * intros r Hr_valid Hr_repr.
        rewrite uf_rank_set_parent_state.
        apply Hrank_bound.
        -- apply (proj1
             (valid_set_parent_state s x
               (uf_parent s (uf_parent s x)) r)).
           exact Hr_valid.
        -- exact Hr_repr.
Qed.
Lemma uf_root_equals_representative__find_root :
  forall s repr_of x,
    uf_abstract s repr_of ->
    valid s x ->
    uf_parent s x = x ->
    x = repr_of x.
Proof.
  intros s repr_of x Habs Hvalid Hroot.
  symmetry.
  eapply repr_of_root; eauto.
Qed.
Lemma uf_state_of_replace_grandparent__find_root :
  forall n parents ranks x,
    0 <= x < n ->
    Zlength parents = n ->
    uf_parent_indices_valid n parents ->
    uf_state_of n
      (replace_Znth x (Znth (Znth x parents 0) parents 0) parents)
      ranks =
    set_parent_state x
      (uf_parent (uf_state_of n parents ranks)
        (uf_parent (uf_state_of n parents ranks) x))
      (uf_state_of n parents ranks).
Proof.
  intros n parents ranks x Hx Hlen Hparents.
  unfold uf_state_of, set_parent_state; simpl.
  f_equal.
  apply functional_extensionality; intro z.
  destruct (Z.eq_dec z x) as [Hzx | Hzx].
  - subst z.
    destruct (Z_le_dec 0 x) as [Hx0 | Hx0]; [|lia].
    destruct (Z_lt_dec x n) as [Hxn | Hxn]; [|lia].
    rewrite Znth_replace_Znth_Same by lia.
    destruct (Hparents x Hx) as [Hp0 Hpn].
    destruct (Z_le_dec 0 (Znth x parents 0)) as [Hgp0 | Hgp0]; [|lia].
    destruct (Z_lt_dec (Znth x parents 0) n) as [Hgpn | Hgpn]; [|lia].
    reflexivity.
  - destruct (Z_le_dec 0 z) as [Hz0 | Hz0].
    + destruct (Z_lt_dec z n) as [Hzn | Hzn].
      * rewrite Znth_replace_Znth_Diff by lia.
        reflexivity.
      * reflexivity.
    + reflexivity.
Qed.
Lemma uf_root_rank_bounds__unite_transitions :
  forall n ps rs repr_of r,
    uf_abstract (uf_state_of n ps rs) repr_of ->
    valid (uf_state_of n ps rs) r ->
    repr_of r = r ->
    0 <= Znth r rs 0 < n.
Proof.
  intros n ps rs repr_of r Habs Hvalid Hroot.
  assert (Hr : 0 <= r < n).
  { unfold valid in Hvalid. simpl in Hvalid. exact Hvalid. }
  pose proof (uf_abstract_inv _ _ Habs) as Hinv.
  pose proof (uf_inv_rank_nonnegative _ Hinv r Hvalid) as Hnonneg.
  pose proof (uf_abstract_rank_class_bound _ _ Habs r Hvalid Hroot) as Hbound.
  unfold uf_state_of in Hnonneg, Hbound; simpl in Hnonneg, Hbound.
  destruct (Z_le_dec 0 r); [| lia].
  destruct (Z_lt_dec r n); [| lia].
  fold (uf_state_of n ps rs) in Hbound.
  assert (Hn : 0 <= n) by lia.
  pose proof (class_size_upper (uf_state_of n ps rs) repr_of r Hn) as Hupper.
  change (class_size (uf_state_of n ps rs) repr_of r <= n) in Hupper.
  lia.
Qed.
Lemma uf_state_of_set_parent__unite_transitions :
  forall n ps rs old new,
    Zlength ps = n ->
    0 <= old < n ->
    uf_state_of n (replace_Znth old new ps) rs =
      set_parent_state old new (uf_state_of n ps rs).
Proof.
  intros n ps rs old new Hlen Hold.
  unfold uf_state_of, set_parent_state; simpl.
  f_equal.
  apply functional_extensionality; intro z.
  destruct (Z_le_dec 0 z) as [Hz0 | Hz0];
    destruct (Z_lt_dec z n) as [Hzn | Hzn];
    destruct (Z.eq_dec z old) as [-> | Hneq]; try lia.
  - rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := old) (j := z) by lia.
    reflexivity.
Qed.
Lemma uf_parent_indices_valid_replace__unite_transitions :
  forall n ps old new,
    Zlength ps = n ->
    0 <= old < n ->
    0 <= new < n ->
    uf_parent_indices_valid n ps ->
    uf_parent_indices_valid n (replace_Znth old new ps).
Proof.
  intros n ps old new Hlen Hold Hnew Hvalid k Hk.
  destruct (Z.eq_dec k old) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    exact Hnew.
  - rewrite Znth_replace_Znth_Diff with (i := old) (j := k) by lia.
    apply Hvalid; exact Hk.
Qed.
Lemma uf_link_lower_rank__unite_transitions :
  forall n ps rs repr_of x y rx ry,
    Zlength ps = n ->
    uf_abstract (uf_state_of n ps rs) repr_of ->
    valid (uf_state_of n ps rs) x ->
    valid (uf_state_of n ps rs) y ->
    rx = repr_of x ->
    ry = repr_of y ->
    rx <> ry ->
    Znth rx rs 0 < Znth ry rs 0 ->
    uf_abstract (uf_state_of n (replace_Znth rx ry ps) rs)
      (link_repr repr_of rx ry) /\
    merge (valid (uf_state_of n (replace_Znth rx ry ps) rs))
      repr_of x y (link_repr repr_of rx ry).
Proof.
  intros n ps rs repr_of x y rx ry Hlen Habs Hx Hy Hrx Hry Hneq Hrank.
  pose proof (uf_abstract_models _ _ Habs x Hx) as Hroot_x.
  pose proof (uf_abstract_models _ _ Habs y Hy) as Hroot_y.
  destruct Hroot_x as [_ [_ [Hvalid_rx Hparent_rx]]].
  destruct Hroot_y as [_ [_ [Hvalid_ry Hparent_ry]]].
  rewrite <- Hrx in Hvalid_rx, Hparent_rx.
  rewrite <- Hry in Hvalid_ry, Hparent_ry.
  assert (Hrank_state :
    uf_rank (uf_state_of n ps rs) rx < uf_rank (uf_state_of n ps rs) ry).
  {
    unfold uf_state_of; simpl.
    unfold valid in Hvalid_rx, Hvalid_ry; simpl in Hvalid_rx, Hvalid_ry.
    destruct (Z_le_dec 0 rx); [| lia].
    destruct (Z_lt_dec rx n); [| lia].
    destruct (Z_le_dec 0 ry); [| lia].
    destruct (Z_lt_dec ry n); [| lia].
    exact Hrank.
  }
  pose proof (uf_abstract_link_root_lt
    (uf_state_of n ps rs) repr_of rx ry Habs Hvalid_rx Hvalid_ry
    Hparent_rx Hparent_ry Hneq Hrank_state) as Hlinked.
  pose proof (merge_link_repr
    (uf_state_of n ps rs) repr_of x y rx ry Hx Hy Hrx Hry Hneq) as Hmerge.
  rewrite <- (uf_state_of_set_parent__unite_transitions
    n ps rs rx ry Hlen ltac:(unfold valid in Hvalid_rx; simpl in Hvalid_rx; exact Hvalid_rx))
    in Hlinked.
  split; [exact Hlinked |].
  eapply merge_transport; [| exact Hmerge].
  intros z Hz.
  unfold valid in *; simpl in *; exact Hz.
Qed.
Lemma uf_state_of_inc_rank__unite_transitions :
  forall n ps rs x,
    Zlength rs = n ->
    0 <= x < n ->
    uf_state_of n ps (replace_Znth x (Znth x rs 0 + 1) rs) =
      inc_rank_state x (uf_state_of n ps rs).
Proof.
  intros n ps rs x Hlen Hx.
  unfold uf_state_of, inc_rank_state, set_rank_state; simpl.
  f_equal.
  apply functional_extensionality; intro z.
  destruct (Z_le_dec 0 z) as [Hz0 | Hz0];
    destruct (Z_lt_dec z n) as [Hzn | Hzn];
    destruct (Z.eq_dec z x) as [-> | Hneq]; try lia.
  - rewrite Znth_replace_Znth_Same by lia.
    destruct (Z_le_dec 0 x); [| lia].
    destruct (Z_lt_dec x n); [reflexivity | lia].
  - rewrite Znth_replace_Znth_Diff with (i := x) (j := z) by lia.
    reflexivity.
Qed.
Lemma uf_link_equal_rank__unite_transitions :
  forall n ps rs repr_of x y rx ry,
    Zlength ps = n ->
    Zlength rs = n ->
    uf_abstract (uf_state_of n ps rs) repr_of ->
    valid (uf_state_of n ps rs) x ->
    valid (uf_state_of n ps rs) y ->
    rx = repr_of x ->
    ry = repr_of y ->
    rx <> ry ->
    Znth rx rs 0 = Znth ry rs 0 ->
    uf_abstract
      (uf_state_of n (replace_Znth ry rx ps)
        (replace_Znth rx (Znth rx rs 0 + 1) rs))
      (link_repr repr_of ry rx) /\
    merge
      (valid
        (uf_state_of n (replace_Znth ry rx ps)
          (replace_Znth rx (Znth rx rs 0 + 1) rs)))
      repr_of x y (link_repr repr_of ry rx).
Proof.
  intros n ps rs repr_of x y rx ry Hlen_ps Hlen_rs Habs Hx Hy
    Hrx Hry Hneq Hrank.
  pose proof (uf_abstract_models _ _ Habs x Hx) as Hroot_x.
  pose proof (uf_abstract_models _ _ Habs y Hy) as Hroot_y.
  destruct Hroot_x as [_ [_ [Hvalid_rx Hparent_rx]]].
  destruct Hroot_y as [_ [_ [Hvalid_ry Hparent_ry]]].
  rewrite <- Hrx in Hvalid_rx, Hparent_rx.
  rewrite <- Hry in Hvalid_ry, Hparent_ry.
  assert (Hrank_state :
    uf_rank (uf_state_of n ps rs) ry = uf_rank (uf_state_of n ps rs) rx).
  {
    unfold uf_state_of; simpl.
    unfold valid in Hvalid_rx, Hvalid_ry; simpl in Hvalid_rx, Hvalid_ry.
    destruct (Z_le_dec 0 ry); [| lia].
    destruct (Z_lt_dec ry n); [| lia].
    destruct (Z_le_dec 0 rx); [| lia].
    destruct (Z_lt_dec rx n); [| lia].
    symmetry; exact Hrank.
  }
  pose proof (uf_abstract_link_root_eq
    (uf_state_of n ps rs) repr_of ry rx Habs Hvalid_ry Hvalid_rx
    Hparent_ry Hparent_rx ltac:(congruence) Hrank_state) as Hlinked.
  pose proof (merge_link_repr
    (uf_state_of n ps rs) repr_of y x ry rx Hy Hx Hry Hrx
    ltac:(congruence)) as Hmerge_yx.
  assert (Hstate :
    uf_state_of n (replace_Znth ry rx ps)
      (replace_Znth rx (Znth rx rs 0 + 1) rs) =
    inc_rank_state rx (set_parent_state ry rx (uf_state_of n ps rs))).
  {
    rewrite (uf_state_of_inc_rank__unite_transitions
      n (replace_Znth ry rx ps) rs rx Hlen_rs
      ltac:(unfold valid in Hvalid_rx; simpl in Hvalid_rx; exact Hvalid_rx)).
    f_equal.
    apply uf_state_of_set_parent__unite_transitions; [exact Hlen_ps |].
    unfold valid in Hvalid_ry; simpl in Hvalid_ry; exact Hvalid_ry.
  }
  rewrite <- Hstate in Hlinked.
  split; [exact Hlinked |].
  apply merge_sym.
  eapply merge_transport; [| exact Hmerge_yx].
  intros z Hz.
  unfold valid in *; simpl in *; exact Hz.
Qed.
Lemma uf_link_higher_rank__unite_transitions :
  forall n ps rs repr_of x y rx ry,
    Zlength ps = n ->
    uf_abstract (uf_state_of n ps rs) repr_of ->
    valid (uf_state_of n ps rs) x ->
    valid (uf_state_of n ps rs) y ->
    rx = repr_of x ->
    ry = repr_of y ->
    rx <> ry ->
    Znth ry rs 0 < Znth rx rs 0 ->
    uf_abstract (uf_state_of n (replace_Znth ry rx ps) rs)
      (link_repr repr_of ry rx) /\
    merge (valid (uf_state_of n (replace_Znth ry rx ps) rs))
      repr_of x y (link_repr repr_of ry rx).
Proof.
  intros n ps rs repr_of x y rx ry Hlen Habs Hx Hy Hrx Hry Hneq Hrank.
  pose proof (uf_link_lower_rank__unite_transitions
    n ps rs repr_of y x ry rx Hlen Habs Hy Hx Hry Hrx
    ltac:(congruence) Hrank) as [Hlinked Hmerge].
  split; [exact Hlinked |].
  apply merge_sym; exact Hmerge.
Qed.
Lemma uf_identity_abstract__kruskal_init :
  forall n parents ranks,
    0 <= n ->
    (forall k, 0 <= k < n ->
      Znth k parents 0 = k /\ Znth k ranks 0 = 0) ->
    uf_abstract (uf_state_of n parents ranks) (fun x => x).
Proof.
  intros n parents ranks Hn Hinit.
  unfold uf_abstract.
  split.
  - intros x Hx. split; [exact Hx | reflexivity].
  - split.
    + split.
      * intros x Hx.
        unfold valid, uf_state_of in Hx |- *; simpl in Hx |- *.
        destruct (Z_le_dec 0 x); [|lia].
        destruct (Z_lt_dec x n); [|lia].
        rewrite (proj1 (Hinit x Hx)).
        exact Hx.
      * split.
        -- intros x Hx.
           unfold valid, uf_state_of in Hx |- *; simpl in Hx |- *.
           destruct (Z_le_dec 0 x); [|lia].
           destruct (Z_lt_dec x n); [|lia].
           rewrite (proj2 (Hinit x Hx)).
           lia.
        -- intros x Hx Hparent.
           unfold valid, uf_state_of in Hx, Hparent |- *; simpl in Hx, Hparent |- *.
           destruct (Z_le_dec 0 x); [|lia].
           destruct (Z_lt_dec x n); [|lia].
           rewrite (proj1 (Hinit x Hx)) in Hparent.
           contradiction.
    + split.
      * intros x Hx.
        pose proof Hx as Hvalid.
        unfold valid, uf_state_of in Hx; simpl in Hx.
        unfold root_of, valid, uf_state_of; simpl.
        repeat split.
        -- lia.
        -- lia.
        -- apply parent_chain_refl. exact Hvalid.
        -- lia.
        -- lia.
        --
           destruct (Z_le_dec 0 x); [|lia].
           destruct (Z_lt_dec x n); [|lia].
           apply (proj1 (Hinit x Hx)).
      * intros r Hr _.
        pose proof Hr as Hvalid.
        unfold valid, uf_state_of in Hr; simpl in Hr.
        unfold uf_state_of; simpl.
        destruct (Z_le_dec 0 r); [|lia].
        destruct (Z_lt_dec r n); [|lia].
        rewrite (proj2 (Hinit r Hr)).
        apply (Z.lt_le_trans 0 1 _); [lia |].
        apply class_size_root_positive; [exact Hvalid | reflexivity].
Qed.
Lemma kruskal_initial_scan_state__kruskal_init :
  forall n m from to wt g edge_order s X,
    2 <= n ->
    array_graph n m from to wt g ->
    KruskalEnv g ->
    initStPred g s ->
    safeExec (initStPred g) (KruskalProg g) X ->
    kruskal_scan_state g edge_order 0 0 s /\
    kruskal_scan_phase g s 0 /\
    union_find_connectivity_matches_state g s (fun x => x) /\
    output_prefix_matches_state g 0 nil nil nil s /\
    safeExec (kruskal_state_is s) (KruskalProg g) X.
Proof.
  intros n m from to wt g edge_order s X Hn Hgraph Henv Hinit Hsafe.
  assert (Hm : 0 <= m).
  { pose proof Hgraph as HG. unfold array_graph in HG. tauto. }
  unfold initStPred in Hinit; subst s.
  assert (Hgreedy : kruskal_greedy_invariant g (initSt g)).
  {
    destruct Henv as [Hg Hconnected Hprogress].
    unfold kruskal_greedy_invariant.
    split.
    - unfold forest_has_no_cycle, initSt; simpl.
      intros u [p [Hpath Hnonempty]].
      destruct p as [|e p]; [contradiction |].
      destruct Hpath as [Hvalid _].
      apply valid_epath_cons_inv in Hvalid as [v [Hstep _]].
      apply step_evalid in Hstep.
      exact (proj1 (Kruskal.initial_forest_evalid g e) Hstep).
    - split.
      + unfold forest_has_mst_extension, initSt; simpl.
      destruct (Algorithms.Prim.Prim.connected_have_mst_in_subgraph
        g Hconnected Hg) as [y Hy].
      exists y. split; [exact Hy |].
      pose proof (is_mst_legal g y Hy) as [_ [_ Hsubeq]].
      destruct Hsubeq as [Hsubv Hsubstep].
      constructor.
      * intros x Hx.
        apply Hsubv.
        exact (proj1 (Kruskal.initial_forest_vvalid g x) Hx).
      * intros u v e Hstep.
        exfalso.
        apply step_evalid in Hstep.
        exact (proj1 (Kruskal.initial_forest_evalid g e) Hstep).
      + split.
        * unfold initSt; simpl.
          unfold gvalid, gvalid_instance, graph_wf; simpl. intros e [].
        * unfold initSt; simpl.
          constructor.
          -- intros x. reflexivity.
          -- unfold step_aux, graph_instance, graph_step. simpl. tauto.
  }
  assert (Hphase : kruskal_scan_phase g (initSt g) 0).
  {
    apply kruskal_scan_phase_from_greedy with (chosen := 0).
    - exact Henv.
    - exact Hgreedy.
    - unfold initSt, graph_edge_count; simpl.
      reflexivity.
    - rewrite (array_graph_vertex_count _ _ _ _ _ _ Hgraph).
      lia.
  }
  split.
  - unfold kruskal_scan_state.
    split.
    + split; [lia |].
      rewrite (array_graph_edge_count _ _ _ _ _ _ Hgraph). exact Hm.
    + split; [exact Hphase |].
      split.
      * unfold initSt, graph_edge_count; simpl. reflexivity.
      * split.
        -- unfold growing_subgraph_of, growing_subgraph_steps, initSt; simpl.
           split.
           ++ intros e He.
              simpl in He. contradiction.
           ++ intros e u v Hstep.
              unfold graph_step in Hstep. simpl in Hstep. tauto.
        -- split; [exact Hgreedy |].
           unfold scanned_prefix_not_selectable. intros k Hk. lia.
  - split; [exact Hphase |].
    split.
    + unfold union_find_connectivity_matches_state, initSt; simpl.
      intros u v Hu Hv. split.
      * intros ->. unfold reachable. reflexivity.
      * intros Hreach.
        destruct (reachable_1n u v Hreach) as [[z [[e Hstep] _]] | Heq].
        -- unfold graph_step in Hstep.
           destruct Hstep as [He _]. simpl in He. contradiction.
        -- exact Heq.
    + split.
      * unfold output_prefix_matches_state, initSt; simpl.
        repeat split; try lia.
      * destruct Hsafe as [hs [Hhs Hsafe]].
        exists hs. split; [|exact Hsafe].
        unfold initStPred in Hhs.
        unfold kruskal_state_is.
        exact Hhs.
Qed.
Lemma In_Znth_index__kruskal_selected_transition :
  forall {A : Type} (l : list A) (x d : A),
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l; induction l as [|a l IH]; intros x d Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + exists 0. rewrite Zlength_cons. split.
      * rewrite Zlength_correct. lia.
      * reflexivity.
    + destruct (IH x d Hin) as [i [Hi Hnth]].
      exists (i + 1). rewrite Zlength_cons. split; [lia|].
      rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia.
      exact Hnth.
Qed.
Lemma current_sorted_edge_facts__kruskal_selected_transition :
  forall n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order i,
    array_graph n m orig_u orig_v orig_w g ->
    after_sorted_edge_of_input m orig_u orig_v orig_w
      edge_u edge_v edge_w edge_order ->
    gvalid g ->
    0 <= i < m ->
    let e := Znth i edge_order (-1) in
    evalid g e /\
    step_aux g e (Znth i edge_u 0) (Znth i edge_v 0) /\
    weight g e = Some (Znth i edge_w 0).
Proof.
  intros n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order i.
  intros Hgraph [Hordered Hsorted] Hg Hi.
  destruct Hordered as
    [Hu0 [Hv0 [Hw0 [Hu [Hv [Hw [Horder [Hperm Hentries]]]]]]]].
  assert (Hin_order : In (Znth i edge_order (-1)) edge_order).
  { apply Znth_In_Zlength. lia. }
  assert (Hin_range : In (Znth i edge_order (-1)) (Zrange 0 m)).
  { eapply Permutation_in; eauto. }
  specialize (Hentries i Hi).
  cbn in Hentries.
  destruct Hentries as [He_range [Heu [Hev Hew]]].
  destruct Hgraph as
    [Hvertices [Hedges [Hn [Hm [Horig_u [Horig_v [Horig_w Hgraph_entries]]]]]]].
  specialize (Hgraph_entries (Znth i edge_order (-1)) Hin_range).
  destruct Hgraph_entries as [Hfrom [Hto Hweight]].
  split.
  - unfold evalid, graph_instance. rewrite Hedges. exact Hin_range.
  - split.
    + unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
        edge_src, edge_dst.
      split.
      * rewrite Hedges. exact Hin_range.
      * split.
        -- destruct (Hg (Znth i edge_order (-1))) as [x [y Hstep]].
           { unfold evalid, graph_instance. rewrite Hedges. exact Hin_range. }
           destruct Hstep as [_ [Hends _]].
           exact Hends.
        -- left. rewrite Hfrom, Hto, Heu, Hev. auto.
    + unfold weight, edge_weight_instance. rewrite Hweight, Hew. reflexivity.
Qed.
Lemma selected_sorted_edge__kruskal_selected_transition :
  forall n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order
      i chosen s repr_of,
    array_graph n m orig_u orig_v orig_w g ->
    after_sorted_edge_of_input m orig_u orig_v orig_w
      edge_u edge_v edge_w edge_order ->
    gvalid g ->
    kruskal_scan_state g edge_order i chosen s ->
    union_find_connectivity_matches_state g s repr_of ->
    repr_of (Znth i edge_u 0) <> repr_of (Znth i edge_v 0) ->
    0 <= i < m ->
    selected_edge_is_min_edge g edge_order i s (Znth i edge_order (-1)) /\
    selected_edge_pair g (Znth i edge_order (-1))
      (Znth i edge_u 0) (Znth i edge_v 0) /\
    weight g (Znth i edge_order (-1)) = Some (Znth i edge_w 0).
Proof.
  intros n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order
    i chosen s repr_of Hgraph Hsorted Hg Hscan Hconn Hneq Hi.
  pose proof (current_sorted_edge_facts__kruskal_selected_transition
    n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order i
    Hgraph Hsorted Hg Hi) as [He [Hstep Hweight]].
  assert (Hselect : state_selectable_edge g s (Znth i edge_order (-1))).
  {
    split; [exact He|].
    intros x y Hxy Hreach.
    assert (Hu_valid : In (Znth i edge_u 0) (graph_vertices g)).
    { change (vvalid g (Znth i edge_u 0)).
      exact (@step_vvalid1 G V E graph_instance gvalid_instance
        stepvalid_instance g _ _ _ Hstep). }
    assert (Hv_valid : In (Znth i edge_v 0) (graph_vertices g)).
    { change (vvalid g (Znth i edge_v 0)).
      exact (@step_vvalid2 G V E graph_instance gvalid_instance
        stepvalid_instance g _ _ _ Hstep). }
    pose proof (step_aux_unique_undirected g (Znth i edge_order (-1))
      (Znth i edge_u 0) (Znth i edge_v 0) x y Hg Hstep Hxy)
      as [[Hx Hy] | [Hx Hy]]; subst x y.
    - apply Hneq.
      apply (proj2 (Hconn _ _ Hu_valid Hv_valid)). exact Hreach.
    - apply Hneq. symmetry.
      apply (proj2 (Hconn _ _ Hv_valid Hu_valid)). exact Hreach.
  }
  split; [|split; assumption].
  unfold selected_edge_is_min_edge. split; [reflexivity|].
  split; [exact Hselect|].
  unfold min_object_of_subset. split; [exact Hselect|].
  intros e' He'.
  destruct Hsorted as [Hordered Hweights].
  destruct Hordered as
    [Hu0 [Hv0 [Hw0 [Hu [Hv [Hw [Horder [Hperm Hentries]]]]]]]].
  destruct Hgraph as
    [Hvertices [Hedges [Hn [Hm [Horig_u [Horig_v [Horig_w Hgraph_entries]]]]]]].
  assert (Hin_range : In e' (Zrange 0 m)).
  { destruct He' as [Hevalid _]. unfold evalid, graph_instance in Hevalid.
    rewrite Hedges in Hevalid. exact Hevalid. }
  assert (Hin_order : In e' edge_order).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin_range]. }
  destruct (In_Znth_index__kruskal_selected_transition edge_order e' (-1)
    Hin_order) as [j [Hj Hjeq]].
  subst e'.
  assert (Hjm : j < m) by lia.
  destruct (Z_lt_ge_dec j i) as [Hji | Hij].
  - destruct Hscan as [_ [_ [_ [_ [_ Hprefix]]]]].
    exfalso. apply (Hprefix j ltac:(lia)).
    exact He'.
  - destruct (Z.eq_dec j i) as [-> | Hneji].
    + apply Z_op_le_refl.
    + specialize (Hweights i j ltac:(lia) ltac:(lia)).
      pose proof (Hentries i Hi) as Hentry_i.
      pose proof (Hentries j ltac:(lia)) as Hentry_j.
      destruct Hentry_i as [_ [_ [_ Hwi]]].
      destruct Hentry_j as [_ [_ [_ Hwj]]].
      assert (Hini : In (Znth i edge_order (-1)) (Zrange 0 m)).
      { apply (Permutation_in (Znth i edge_order (-1)) Hperm).
        apply Znth_In_Zlength. lia. }
      pose proof (Hgraph_entries (Znth i edge_order (-1)) Hini)
        as Hgraph_i.
      pose proof (Hgraph_entries (Znth j edge_order (-1)) Hin_range)
        as Hgraph_j.
      destruct Hgraph_i as [_ [_ Hgwi]].
      destruct Hgraph_j as [_ [_ Hgwj]].
      unfold weight, edge_weight_instance.
      rewrite Hgwi, Hgwj, <- Hwi, <- Hwj.
      exact Hweights.
Qed.
Lemma Znth_app_single_old__kruskal_selected_transition :
  forall {A : Type} (l : list A) (x d : A) i,
    0 <= i < Zlength l ->
    Znth i (l ++ x :: nil) d = Znth i l d.
Proof.
  intros A l; induction l as [|a l IH]; intros x d i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne]; [reflexivity|].
    change (Znth i (a :: (l ++ x :: nil)) d = Znth i (a :: l) d).
    rewrite !Znth_cons by lia. apply IH. lia.
Qed.
Lemma Znth_app_single_new__kruskal_selected_transition :
  forall {A : Type} (l : list A) (x d : A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A l; induction l as [|a l IH]; intros x d.
  - reflexivity.
  - rewrite Zlength_cons.
    change (Znth (Zlength l + 1) (a :: (l ++ x :: nil)) d = x).
    rewrite Znth_cons.
    + replace (Zlength l + 1 - 1) with (Zlength l) by lia.
      exact (IH x d).
    + rewrite Zlength_correct. lia.
Qed.
Lemma Zlength_app_single__kruskal_selected_transition :
  forall {A : Type} (l : list A) (x : A),
    Zlength (l ++ x :: nil) = Zlength l + 1.
Proof.
  intros A l; induction l as [|a l IH]; intros x.
  - reflexivity.
  - change (Zlength (a :: (l ++ x :: nil)) = Zlength (a :: l) + 1).
    rewrite !Zlength_cons, IH. lia.
Qed.
Lemma output_prefix_matches_state_append__kruskal_selected_transition :
  forall g chosen out_u out_v out_w s u v w e,
    output_prefix_matches_state g chosen out_u out_v out_w s ->
    gvalid s.(Kruskal.graph_in_state) ->
    ~ evalid s.(Kruskal.graph_in_state) e ->
    step_aux g e u v ->
    weight g e = Some w ->
    output_prefix_matches_state g (chosen + 1)
      (out_u ++ u :: nil) (out_v ++ v :: nil) (out_w ++ w :: nil)
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |}.
Proof.
  intros g chosen out_u out_v out_w s u v w e Hout Hvalid Hnew
    Hstep_g Hweight.
  destruct Hout as [Hchosen [Hlu [Hlv [Hlw [Hat Hall]]]]].
  repeat split.
  - lia.
  - rewrite Zlength_app_single__kruskal_selected_transition, Hlu. lia.
  - rewrite Zlength_app_single__kruskal_selected_transition, Hlv. lia.
  - rewrite Zlength_app_single__kruskal_selected_transition, Hlw. lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j chosen) as [Hjold | Hjnew].
    + destruct (Hat j ltac:(lia)) as [a [Ha [Hastep Haweight]]].
      exists a. split.
      * simpl. apply (proj2 (add_edge_graph_evalid_any
          s.(Kruskal.graph_in_state) u v e a)). auto.
      * split.
        -- rewrite !Znth_app_single_old__kruskal_selected_transition by lia.
           simpl. apply (proj2 (add_edge_graph_step_any
             s.(Kruskal.graph_in_state) u v e
             (Znth j out_u 0) (Znth j out_v 0) a Hvalid Hnew)). auto.
        -- rewrite !Znth_app_single_old__kruskal_selected_transition by lia.
           exact Haweight.
    + assert (j = chosen) by lia. subst j.
      exists e. split.
      * simpl. apply (proj2 (add_edge_graph_evalid_any
          s.(Kruskal.graph_in_state) u v e e)). auto.
      * split.
        -- replace (Znth chosen (out_u ++ u :: nil) 0) with u by
             (rewrite <- Hlu; symmetry; apply Znth_app_single_new__kruskal_selected_transition).
           replace (Znth chosen (out_v ++ v :: nil) 0) with v by
             (rewrite <- Hlv; symmetry; apply Znth_app_single_new__kruskal_selected_transition).
           simpl. apply (proj2 (add_edge_graph_step_any
             s.(Kruskal.graph_in_state) u v e u v e Hvalid Hnew)).
           right. auto.
        -- replace (Znth chosen (out_w ++ w :: nil) 0) with w by
             (rewrite <- Hlw; symmetry; apply Znth_app_single_new__kruskal_selected_transition).
           exact Hweight.
  - intros a Ha.
    simpl in Ha.
    apply (proj1 (add_edge_graph_evalid_any
      s.(Kruskal.graph_in_state) u v e a)) in Ha.
    destruct Ha as [Haold | ->].
    + destruct (Hall a Haold) as [j [Hj [Hastep Haweight]]].
      exists j. split; [lia|]. split.
      * rewrite !Znth_app_single_old__kruskal_selected_transition by lia.
        simpl. apply (proj2 (add_edge_graph_step_any
          s.(Kruskal.graph_in_state) u v e
          (Znth j out_u 0) (Znth j out_v 0) a Hvalid Hnew)). auto.
      * rewrite !Znth_app_single_old__kruskal_selected_transition by lia.
        exact Haweight.
    + exists chosen. split; [lia|]. split.
      * replace (Znth chosen (out_u ++ u :: nil) 0) with u by
          (rewrite <- Hlu; symmetry; apply Znth_app_single_new__kruskal_selected_transition).
        replace (Znth chosen (out_v ++ v :: nil) 0) with v by
          (rewrite <- Hlv; symmetry; apply Znth_app_single_new__kruskal_selected_transition).
        simpl. apply (proj2 (add_edge_graph_step_any
          s.(Kruskal.graph_in_state) u v e u v e Hvalid Hnew)).
        right. auto.
      * replace (Znth chosen (out_w ++ w :: nil) 0) with w by
          (rewrite <- Hlw; symmetry; apply Znth_app_single_new__kruskal_selected_transition).
        exact Hweight.
Qed.
Lemma reachable_sym__kruskal_selected_transition :
  forall g x y, reachable g x y -> reachable g y x.
Proof.
  intros g x y Hreach.
  unfold reachable in *.
  induction_1n Hreach.
  - reflexivity.
  - transitivity_n1 x0; auto.
    unfold step in *. destruct H as [a H].
    exists a. eapply step_sym; eauto.
Qed.
Lemma add_edge_union_connectivity__kruskal_selected_transition :
  forall g s repr_of repr_of' D u v e,
    gvalid s.(Kruskal.graph_in_state) ->
    subgraph_vertex_eq s.(Kruskal.graph_in_state) g ->
    union_find_connectivity_matches_state g s repr_of ->
    (forall x, In x (graph_vertices g) -> D x) ->
    merge D repr_of u v repr_of' ->
    step_aux g e u v ->
    ~ evalid s.(Kruskal.graph_in_state) e ->
    union_find_connectivity_matches_state g
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |} repr_of'.
Proof.
  intros g s repr_of repr_of' D u v e Hvalid Hvertices Hconn Hdomain
    Hmerge Hstep_g Hnew a b Ha Hb.
  assert (Hu : In u (graph_vertices g)).
  { change (vvalid g u).
    exact (@step_vvalid1 G V E graph_instance gvalid_instance
      stepvalid_instance g e u v Hstep_g). }
  assert (Hv : In v (graph_vertices g)).
  { change (vvalid g v).
    exact (@step_vvalid2 G V E graph_instance gvalid_instance
      stepvalid_instance g e u v Hstep_g). }
  assert (Hold_sub : forall x y a0,
      step_aux s.(Kruskal.graph_in_state) a0 x y ->
      step_aux (add_edge_graph s.(Kruskal.graph_in_state) u v e) a0 x y).
  { intros x y a0 Hxy.
    apply (proj2 (add_edge_graph_step_any _ _ _ _ _ _ _ Hvalid Hnew)).
    auto. }
  split.
  - intros Hab.
    pose proof (proj1 (Hmerge a b (Hdomain a Ha) (Hdomain b Hb)) Hab)
      as [Hold | [Hcross | Hcross]].
    + apply (proj1 (Hconn a b Ha Hb)) in Hold.
      eapply sub_reachable; eauto.
    + destruct Hcross as [Hau Hbv].
      apply (proj1 (Hconn a u Ha Hu)) in Hau.
      apply (proj1 (Hconn b v Hb Hv)) in Hbv.
      eapply reachable_trans.
      * eapply sub_reachable; eauto.
      * eapply step_reachable_reachable.
        -- apply step_trivial with (e := e).
           apply (proj2 (add_edge_graph_step_any _ _ _ _ _ _ _
             Hvalid Hnew)). right. auto.
        -- apply reachable_sym__kruskal_selected_transition.
           eapply sub_reachable; eauto.
    + destruct Hcross as [Hav Hbu].
      apply (proj1 (Hconn a v Ha Hv)) in Hav.
      apply (proj1 (Hconn b u Hb Hu)) in Hbu.
      eapply reachable_trans.
      * eapply sub_reachable; eauto.
      * eapply step_reachable_reachable.
        -- apply step_trivial with (e := e).
           apply (proj2 (add_edge_graph_step_any _ _ _ _ _ _ _
             Hvalid Hnew)). right. auto.
        -- apply reachable_sym__kruskal_selected_transition.
           eapply sub_reachable; eauto.
  - intros Hreach.
    assert (Hstep_repr : forall x y a0,
      step_aux (add_edge_graph s.(Kruskal.graph_in_state) u v e) a0 x y ->
      repr_of' x = repr_of' y).
    {
      intros x y a0 Hxy.
      assert (Hx : In x (graph_vertices g)).
      { pose proof (@step_vvalid1 G V E graph_instance gvalid_instance
          stepvalid_instance _ a0 x y Hxy) as Hxnew.
        rewrite add_edge_graph_vvalid in Hxnew.
        destruct Hxnew as [Hxold | [-> | ->]]; auto.
        apply Hvertices. exact Hxold. }
      assert (Hy : In y (graph_vertices g)).
      { pose proof (@step_vvalid2 G V E graph_instance gvalid_instance
          stepvalid_instance _ a0 x y Hxy) as Hynew.
        rewrite add_edge_graph_vvalid in Hynew.
        destruct Hynew as [Hyold | [-> | ->]]; auto.
        apply Hvertices. exact Hyold. }
      apply (proj2 (Hmerge x y (Hdomain x Hx) (Hdomain y Hy))).
      apply (proj1 (add_edge_graph_step_any _ _ _ _ _ _ _ Hvalid Hnew))
        in Hxy.
      destruct Hxy as [Hxy | [-> [[-> ->] | [-> ->]]]].
      - left. unfold same_class.
        apply (proj2 (Hconn x y Hx Hy)).
        apply step_rt. apply step_trivial with (e := a0). exact Hxy.
      - right; left. split; unfold same_class; reflexivity.
      - right; right. split; unfold same_class; reflexivity.
    }
    unfold reachable in Hreach.
    induction_1n Hreach.
    + reflexivity.
    + destruct H as [edge Haux].
      assert (Ha0 : In a0 (graph_vertices g)).
      { pose proof (@step_vvalid2 G V E graph_instance gvalid_instance
          stepvalid_instance _ edge a1 a0 Haux) as Ha0new.
        change (In a0 (u :: v :: graph_vertices s.(Kruskal.graph_in_state)))
          in Ha0new.
        destruct Ha0new as [-> | [-> | Ha0old]]; auto.
        apply Hvertices. exact Ha0old. }
      transitivity (repr_of' a0).
      * apply Hstep_repr with (a0 := edge). exact Haux.
      * eapply IHrt; eauto.
Qed.

Lemma add_edge_uf_merge_connectivity__kruskal_selected_transition :
  forall n m orig_u orig_v orig_w g s repr_of repr_of' u v e,
    array_graph n m orig_u orig_v orig_w g ->
    gvalid s.(Kruskal.graph_in_state) ->
    subgraph_vertex_eq s.(Kruskal.graph_in_state) g ->
    union_find_connectivity_matches_state g s repr_of ->
    uf_merge n repr_of u v repr_of' ->
    step_aux g e u v ->
    ~ evalid s.(Kruskal.graph_in_state) e ->
    union_find_connectivity_matches_state g
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |} repr_of'.
Proof.
  intros n m orig_u orig_v orig_w g s repr_of repr_of' u v e
    Hgraph Hvalid Hvertices Hconn Hmerge Hstep Hnew.
  eapply add_edge_union_connectivity__kruskal_selected_transition
    with (D := uf_domain n); eauto.
  - intros x Hx.
    eapply array_graph_vertex_in_uf_domain; eauto.
  - apply uf_merge_domain_merge.
    exact Hmerge.
Qed.
Lemma kruskal_union_add_edge_transition__kruskal_selected_transition :
  forall g edge_order i chosen s u v e,
    KruskalEnv g ->
    kruskal_scan_state g edge_order i chosen s ->
    selected_edge_is_min_edge g edge_order i s e ->
    selected_edge_pair g e u v ->
    i < graph_edge_count g ->
    chosen < graph_vertex_count g - 1 ->
    let s_next : St :=
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |} in
    selected_edge_add_to_mst s s_next u v e /\
    kruskal_scan_state g edge_order (i + 1) (chosen + 1) s_next /\
    kruskal_scan_phase g s_next (chosen + 1).
Proof.
  intros g edge_order i chosen s u v e Henv Hscan Hselected Hpair
    Hi_strict Hchosen_strict.
  cbn.
  destruct Hscan as
    [Hi_bounds [Hphase [Hcount [Hgrowing [Hgreedy Hprefix]]]]].
  destruct Hgrowing as [Hedge_sub Hstep_sub].
  destruct Hgreedy as [Hacyclic [Hextension [Hvalid Hvertexeq]]].
  destruct Hselected as [Heq [Hselect Hmin]].
  destruct Hselect as [He_input Hnot_reachable].
  assert (Hnew : ~ evalid s.(Kruskal.graph_in_state) e).
  {
    intros He_old.
    destruct (Hvalid e He_old) as [x [y Hstep_old]].
    apply (Hnot_reachable x y (Hstep_sub _ _ _ Hstep_old)).
    apply step_rt. apply step_trivial with (e := e). exact Hstep_old.
  }
  assert (Hu_old : vvalid s.(Kruskal.graph_in_state) u).
  { apply Hvertexeq. eapply step_vvalid1; eauto. }
  assert (Hv_old : vvalid s.(Kruskal.graph_in_state) v).
  { apply Hvertexeq. eapply step_vvalid2; eauto. }
  assert (Hadd : addEdge s.(Kruskal.graph_in_state)
      (add_edge_graph s.(Kruskal.graph_in_state) u v e) u v e).
  { apply add_edge_graph_addEdge_any; auto. }
  assert (Hvalid_next :
      gvalid (add_edge_graph s.(Kruskal.graph_in_state) u v e)).
  { apply add_edge_graph_gvalid; auto. }
  assert (Hgreedy_core :
      forest_has_no_cycle (add_edge_graph s.(Kruskal.graph_in_state) u v e) /\
      forest_has_mst_extension g
        (add_edge_graph s.(Kruskal.graph_in_state) u v e)).
  {
    eapply GraphLib.examples.kruskal.kruskal_step with (r := g).
    - exact (kruskal_graph_valid g Henv).
    - exact (conj Hvalid (conj Hacyclic Hextension)).
    - exact Hpair.
    - exact Hadd.
    - exact Hmin.
  }
  assert (Hvertexeq_next : subgraph_vertex_eq
      (add_edge_graph s.(Kruskal.graph_in_state) u v e) g).
  {
    constructor.
    - intros x. rewrite add_edge_graph_vvalid.
      split.
      + intros [Hx | [Hx | Hx]].
        * apply Hvertexeq. exact Hx.
        * subst x. eapply step_vvalid1. exact Hpair.
        * subst x. eapply step_vvalid2. exact Hpair.
      + intros Hx. left. apply Hvertexeq. exact Hx.
    - intros x y a Hxy.
      apply (proj1 (add_edge_graph_step_any _ _ _ _ _ _ _ Hvalid Hnew))
        in Hxy.
      destruct Hxy as [Hxy | [-> [[-> ->] | [-> ->]]]].
      + apply Hstep_sub. exact Hxy.
      + exact Hpair.
      + apply step_sym. exact Hpair.
  }
  assert (Hgrowing_next : growing_subgraph_of g
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |}).
  {
    split.
    - intros a Ha. simpl in Ha.
      apply (proj1 (add_edge_graph_evalid_any
        s.(Kruskal.graph_in_state) u v e a)) in Ha.
      destruct Ha as [Ha | ->]; auto.
    - intros a x y Hxy. simpl in Hxy.
      apply (proj1 (add_edge_graph_step_any
        s.(Kruskal.graph_in_state) u v e x y a Hvalid Hnew))
        in Hxy.
      destruct Hxy as [Hxy | [-> [[-> ->] | [-> ->]]]].
      + apply Hstep_sub. exact Hxy.
      + exact Hpair.
      + apply step_sym. exact Hpair.
  }
  assert (Hcount_next : graph_edge_count
      (add_edge_graph s.(Kruskal.graph_in_state) u v e) = chosen + 1).
  { unfold graph_edge_count in Hcount |- *. unfold add_edge_graph. simpl.
    rewrite Zlength_cons, <- Hcount. lia. }
  assert (Hgreedy_next : kruskal_greedy_invariant g
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |}).
  { destruct Hgreedy_core as [Hacyclic_next Hextension_next].
    exact (conj Hacyclic_next
      (conj Hextension_next (conj Hvalid_next Hvertexeq_next))). }
  assert (Hphase_next : kruskal_scan_phase g
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |}
      (chosen + 1)).
  {
    eapply kruskal_scan_phase_from_greedy.
    - exact Henv.
    - exact Hgreedy_next.
    - simpl. symmetry. exact Hcount_next.
    - destruct Hphase as [Hchosen_bounds _]. lia.
  }
  assert (Hprefix_next : scanned_prefix_not_selectable g edge_order (i + 1)
      {| Kruskal.graph_in_state :=
           add_edge_graph s.(Kruskal.graph_in_state) u v e |}).
  {
    intros k Hk Hselect_new.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    - apply (Hprefix k ltac:(lia)).
      destruct Hselect_new as [He_k Hnr_k]. split; [exact He_k|].
      intros x y Hxy Hreach_old.
      apply (Hnr_k x y Hxy).
      eapply (sub_reachable s.(Kruskal.graph_in_state)
        (add_edge_graph s.(Kruskal.graph_in_state) u v e)
        (g_valid1 := Hvalid)).
      + intros p q a Hpq.
        apply (proj2 (add_edge_graph_step_any
          s.(Kruskal.graph_in_state) u v e p q a Hvalid Hnew)).
        left. exact Hpq.
      + exact Hreach_old.
    - assert (k = i) by lia. subst k. rewrite <- Heq in Hselect_new.
      destruct Hselect_new as [_ Hnr_new].
      apply (Hnr_new u v Hpair).
      apply step_rt. apply step_trivial with (e := e).
      apply (proj2 (add_edge_graph_step_any _ _ _ _ _ _ _ Hvalid Hnew)).
      right. auto.
  }
  split; [exact Hadd|]. split; [|exact Hphase_next].
  assert (Hi_next : 0 <= i + 1 <= graph_edge_count g) by lia.
  assert (Hchosen_count_next : chosen + 1 = graph_edge_count
      (add_edge_graph s.(Kruskal.graph_in_state) u v e)).
  { symmetry. exact Hcount_next. }
  exact (conj Hi_next (conj Hphase_next
    (conj Hchosen_count_next (conj Hgrowing_next
      (conj Hgreedy_next Hprefix_next))))).
Qed.
Lemma safeExec_kruskal_selected_step__kruskal_selected_transition :
  forall g edge_order i s s_next e u v X,
    selected_edge_is_min_edge g edge_order i s e ->
    selected_edge_pair g e u v ->
    selected_edge_add_to_mst s s_next u v e ->
    safeExec (kruskal_state_is s) (KruskalProg g) X ->
    safeExec (kruskal_state_is s_next) (KruskalProg g) X.
Proof.
  intros g edge_order i s s_next e u v X Hselected Hpair Hadd Hsafe.
  destruct Hselected as [_ [Hselect Hmin]].
  unfold KruskalProg, Kruskal.Kruskal in Hsafe |- *.
  pose proof (@safeExec_proequiv St unit _ _ _ _
    (while_unfold _ _) Hsafe) as Hchoice.
  apply safeExec_choice_l in Hchoice.
  eapply safeExec_testst_bind in Hchoice.
  2:{ intros st ->. exists e. exact Hselect. }
  unfold Kruskal.get_min_edge in Hchoice.
  rewrite bind_assoc in Hchoice.
  eapply safeExec_get_bind with (a := e) in Hchoice.
  2:{ intros st ->. exact Hmin. }
  rewrite bind_assoc in Hchoice.
  eapply safeExec_get_bind with (a := (u, v)) in Hchoice.
  2:{ intros st ->. exact Hpair. }
  cbn in Hchoice.
  unfold Kruskal.add_to_mst in Hchoice.
  unfold safeExec, safe in Hchoice |- *.
  destruct Hchoice as [st [Hst Hchoice]].
  unfold kruskal_state_is in Hst. subst st.
  exists s_next. split; [reflexivity|].
  rewrite wp_bind in Hchoice.
  rewrite wp_update in Hchoice.
  apply Hchoice. exact Hadd.
Qed.
Lemma selected_edge_not_in_forest__kruskal_selected_transition :
  forall g edge_order i chosen s e,
    gvalid s.(Kruskal.graph_in_state) ->
    kruskal_scan_state g edge_order i chosen s ->
    selected_edge_is_min_edge g edge_order i s e ->
    ~ evalid s.(Kruskal.graph_in_state) e.
Proof.
  intros g edge_order i chosen s e Hvalid Hscan
    [_ [[_ Hnot_reachable] _]] Hold.
  destruct Hscan as [_ [_ [_ [[_ Hstep_sub] _]]]].
  destruct (Hvalid e Hold) as [u [v Hstep]].
  apply (Hnot_reachable u v (Hstep_sub _ _ _ Hstep)).
  apply step_rt. apply step_trivial with (e := e). exact Hstep.
Qed.
Lemma selected_edge_pair_vertices_range__kruskal_selected_transition :
  forall n m orig_u orig_v orig_w g e u v,
    array_graph n m orig_u orig_v orig_w g ->
    selected_edge_pair g e u v ->
    0 <= u < n /\ 0 <= v < n.
Proof.
  intros n m orig_u orig_v orig_w g e u v Hgraph Hpair.
  destruct Hgraph as [Hvertices _].
  destruct Hpair as [_ [[Hu Hv] [[Hu_eq Hv_eq] | [Hu_eq Hv_eq]]]];
    subst u v;
  rewrite Hvertices, <- !In_Zrange in Hu, Hv.
  - exact (conj Hu Hv).
  - exact (conj Hv Hu).
Qed.
Lemma sorted_edge_endpoints_range__kruskal_scan_control :
  forall n m orig_u orig_v orig_w edge_u edge_v edge_w edge_order g i,
    array_graph n m orig_u orig_v orig_w g ->
    KruskalEnv g ->
    after_sorted_edge_of_input m orig_u orig_v orig_w
      edge_u edge_v edge_w edge_order ->
    0 <= i < m ->
    0 <= Znth i edge_u 0 < n /\
    0 <= Znth i edge_v 0 < n.
Proof.
  intros n m orig_u orig_v orig_w edge_u edge_v edge_w edge_order g i
    Hgraph Henv Hsorted Hi.
  destruct Henv as [Hg _ _].
  destruct Hsorted as [Hordered _].
  unfold edge_arrays_ordered_by in Hordered.
  destruct Hordered as
    [_ [_ [_ [_ [_ [_ [_ [_ Hmapping]]]]]]]].
  specialize (Hmapping i Hi).
  cbn in Hmapping.
  destruct Hmapping as [He [Hu [Hv _]]].
  pose proof
    (array_graph_edge_endpoints_range n m orig_u orig_v orig_w g
      (Znth i edge_order (-1)) Hgraph Hg He) as [Horig_u Horig_v].
  rewrite Hu, Hv.
  split; assumption.
Qed.
Lemma scanned_prefix_extend_nonselectable__kruskal_scan_control :
  forall n m orig_u orig_v orig_w edge_u edge_v edge_w edge_order g
      i chosen s repr_of,
    array_graph n m orig_u orig_v orig_w g ->
    KruskalEnv g ->
    after_sorted_edge_of_input m orig_u orig_v orig_w
      edge_u edge_v edge_w edge_order ->
    kruskal_scan_state g edge_order i chosen s ->
    union_find_connectivity_matches_state g s repr_of ->
    0 <= i < m ->
    repr_of (Znth i edge_u 0) = repr_of (Znth i edge_v 0) ->
    kruskal_scan_state g edge_order (i + 1) chosen s.
Proof.
  intros n m orig_u orig_v orig_w edge_u edge_v edge_w edge_order g
    i chosen s repr_of Hgraph Henv Hsorted Hstate Hconnect Hi Hrepr.
  pose proof Hgraph as Hgraph_fields.
  pose proof Hsorted as Hsorted_fields.
  pose proof
    (sorted_edge_endpoints_range__kruskal_scan_control
      n m orig_u orig_v orig_w edge_u edge_v edge_w edge_order g i
      Hgraph Henv Hsorted Hi) as [Hu_range Hv_range].
  destruct Hstate as
    [Hi_state [Hphase [Hchosen [Hgrowing [Hgreedy Hscanned]]]]].
  split.
  - rewrite (array_graph_edge_count n m orig_u orig_v orig_w g Hgraph).
    lia.
  - split; [exact Hphase |].
    split; [exact Hchosen |].
    split; [exact Hgrowing |].
    split; [exact Hgreedy |].
    unfold scanned_prefix_not_selectable in *.
    intros k Hk Hselectable.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + eapply Hscanned; eauto; lia.
    + assert (Hki : k = i) by lia.
      subst k.
      destruct Hsorted_fields as [Hordered _].
      unfold edge_arrays_ordered_by in Hordered.
      destruct Hordered as
        [_ [_ [_ [_ [_ [_ [_ [_ Hmapping]]]]]]]].
      specialize (Hmapping i Hi).
      cbn in Hmapping.
      destruct Hmapping as [He_range [Hu [Hv _]]].
      destruct Hgraph_fields as
        [Hvertices [Hedges [_ [_ [_ [_ [_ Hentries]]]]]]].
      assert (He_in : In (Znth i edge_order (-1)) (Zrange 0 m)).
      { rewrite <- In_Zrange. lia. }
      specialize (Hentries (Znth i edge_order (-1)) He_in).
      destruct Hentries as [Hfrom [Hto _]].
      assert (Hevalid : evalid g (Znth i edge_order (-1))).
      {
        unfold evalid, graph_instance.
        rewrite Hedges.
        exact He_in.
      }
      assert (Huv : edge_endpoints_valid g (Znth i edge_order (-1))).
      {
        unfold edge_endpoints_valid, edge_src, edge_dst.
        rewrite Hvertices, Hfrom, Hto, <- Hu, <- Hv.
        split; rewrite <- In_Zrange; lia.
      }
      assert (Hstep :
        step_aux g (Znth i edge_order (-1))
          (Znth i edge_u 0) (Znth i edge_v 0)).
      {
        unfold step_aux, graph_instance, graph_step.
        split; [exact Hevalid |].
        split; [exact Huv |].
        left.
        unfold edge_src, edge_dst.
        rewrite Hfrom, Hto, <- Hu, <- Hv.
        auto.
      }
      destruct Hselectable as [_ Hno_path].
      specialize (Hno_path (Znth i edge_u 0) (Znth i edge_v 0) Hstep).
      apply Hno_path.
      assert (Hu_valid : In (Znth i edge_u 0) (graph_vertices g)).
      { rewrite Hvertices, <- In_Zrange. lia. }
      assert (Hv_valid : In (Znth i edge_v 0) (graph_vertices g)).
      { rewrite Hvertices, <- In_Zrange. lia. }
      pose proof
        (Hconnect (Znth i edge_u 0) (Znth i edge_v 0)
          Hu_valid Hv_valid) as Hconnected_iff.
      apply (proj1 Hconnected_iff).
      exact Hrepr.
Qed.
Lemma kruskal_completed_output_graph__kruskal_exit_result :
  forall n m orig_u orig_v orig_w g chosen out_u out_v out_w s,
    array_graph n m orig_u orig_v orig_w g ->
    chosen = n - 1 ->
    output_prefix_matches_state g chosen out_u out_v out_w s ->
    kruskal_result_graph_matches_array
      out_u out_v out_w g s.(Kruskal.graph_in_state).
Proof.
  intros n m orig_u orig_v orig_w g chosen out_u out_v out_w s
    Hgraph Hchosen Houtput.
  pose proof (array_graph_vertex_count _ _ _ _ _ _ Hgraph) as Hvertices.
  unfold graph_vertex_count in Hvertices.
  unfold output_prefix_matches_state in Houtput.
  destruct Houtput as
    [Hnonneg [Hlen_u [Hlen_v [Hlen_w [Hslots Hedges]]]]].
  unfold kruskal_result_graph_matches_array.
  rewrite Hvertices.
  repeat split; try lia.
  - intros i Hi.
    apply Hslots.
    rewrite <- In_Zrange in Hi.
    lia.
  - intros e He.
    specialize (Hedges e He) as [i [Hi [Hstep Hweight]]].
    exists i.
    split.
    + rewrite <- In_Zrange.
      lia.
    + auto.
Qed.
Lemma KruskalProg_complete_return__kruskal_exit_result :
  forall g s,
    (~ exists e, state_selectable_edge g s e) ->
    KruskalProg g s tt s.
Proof.
  intros g s Hcomplete.
  unfold KruskalProg, Kruskal.Kruskal.
  lazymatch goal with
  | |- context [whileP ?cond ?body] =>
      pose proof (while_unfold cond body) as Hunfold;
      apply Sets_equiv_Sets_included in Hunfold;
      destruct Hunfold as [_ Hunfold];
      apply Hunfold
  end.
  unfold choice, test, StateRelMonad.bind, StateRelMonad.ret.
  right.
  exists tt, s.
  split.
  - split; [exact Hcomplete | reflexivity].
  - split; reflexivity.
Qed.
Lemma In_Znth_Zlength__kruskal_exit_result :
  forall (A : Type) (xs : list A) (x dflt : A),
    In x xs ->
    exists i, 0 <= i < Zlength xs /\ Znth i xs dflt = x.
Proof.
  intros A xs x dflt Hin.
  apply In_nth with (d := dflt) in Hin as [i [Hi Hnth]].
  exists (Z.of_nat i).
  split.
  - rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
Qed.
Lemma kruskal_exhausted_scan_complete__kruskal_exit_result :
  forall n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order
      i chosen s,
    array_graph n m orig_u orig_v orig_w g ->
    after_sorted_edge_of_input
      m orig_u orig_v orig_w edge_u edge_v edge_w edge_order ->
    kruskal_scan_state g edge_order i chosen s ->
    i >= m ->
    chosen = n - 1.
Proof.
  intros n m orig_u orig_v orig_w g edge_u edge_v edge_w edge_order
    i chosen s Hgraph Hordered Hscan Hi.
  pose proof (array_graph_vertex_count _ _ _ _ _ _ Hgraph) as Hvertices.
  unfold after_sorted_edge_of_input, edge_arrays_ordered_by in Hordered.
  destruct Hordered as
    [[_ [_ [_ [_ [_ [_ [Horder_len [Hperm _]]]]]]]] _].
  unfold kruskal_scan_state in Hscan.
  destruct Hscan as [_ [Hphase [_ [_ [_ Hscanned]]]]].
  unfold kruskal_scan_phase in Hphase.
  destruct Hphase as [Hbounds Hguard].
  rewrite Hvertices in Hbounds, Hguard.
  apply Z.le_antisymm; [lia |].
  apply Z.nlt_ge.
  intro Hlt.
  apply (proj2 Hguard) in Hlt as [e Hselectable].
  assert (He_input : In e (Zrange 0 m)).
  {
    destruct Hselectable as [Hevalid _].
    unfold evalid, graph_instance in Hevalid.
    destruct Hgraph as [_ [Hedges _]].
    rewrite <- Hedges.
    exact Hevalid.
  }
  assert (He_order : In e edge_order).
  {
    eapply Permutation_in.
    - exact (Permutation_sym Hperm).
    - exact He_input.
  }
  destruct (In_Znth_Zlength__kruskal_exit_result
    Z edge_order e (-1) He_order) as [k [Hk Hnth]].
  unfold scanned_prefix_not_selectable in Hscanned.
  rewrite <- Hnth in Hselectable.
  assert (Hki : 0 <= k < i) by lia.
  exact (Hscanned k Hki Hselectable).
Qed.
Lemma safeExec_Kruskal_complete_return__kruskal_exit_result :
  forall g s X,
    (~ exists e, state_selectable_edge g s e) ->
    safeExec (kruskal_state_is s) (KruskalProg g) X ->
    safeExec
      (kruskal_state_graph_matches s.(Kruskal.graph_in_state))
      (return tt) X.
Proof.
  intros g s X Hcomplete Hsafe.
  unfold safeExec, safe in *.
  destruct Hsafe as [hs [Hstate Hwp]].
  unfold kruskal_state_is in Hstate.
  subst hs.
  exists s.
  split.
  - unfold kruskal_state_graph_matches.
    reflexivity.
  - rewrite wp_ret.
    eapply wp_spec.
    + apply KruskalProg_complete_return__kruskal_exit_result.
      exact Hcomplete.
    + exact Hwp.
Qed.
Lemma safeExec_kruskal_return_is_mst__high_level_refinement :
  forall g rg,
    KruskalEnv g ->
    safeExec (initStPred g) (KruskalProg g)
      (fun _ s => return_is_mst g s.(Kruskal.graph_in_state)) /\
    (safeExec (kruskal_state_graph_matches rg) (return tt)
       (fun _ s => return_is_mst g s.(Kruskal.graph_in_state)) ->
     return_is_mst g rg).
Proof.
  intros g rg Henv.
  split.
  - eapply safeExec_X_subset.
    + apply Hoare_result_state.
      apply Kruskal_correct_concrete.
      exact Henv.
    + apply safeExec_result_state.
      exists (initSt g).
      reflexivity.
  - intros Hsafe.
    apply safeExec_ret in Hsafe.
    destruct Hsafe as [s [Hgraph Hmst]].
    unfold kruskal_state_graph_matches in Hgraph.
    subst rg.
    exact Hmst.
Qed.
